/*-
 *   BSD LICENSE
 *
 *   Copyright(c) 2017 Intel Corporation. All rights reserved.
 *
 *   Redistribution and use in source and binary forms, with or without
 *   modification, are permitted provided that the following conditions
 *   are met:
 *
 *     * Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 *     * Redistributions in binary form must reproduce the above copyright
 *       notice, this list of conditions and the following disclaimer in
 *       the documentation and/or other materials provided with the
 *       distribution.
 *     * Neither the name of Intel Corporation nor the names of its
 *       contributors may be used to endorse or promote products derived
 *       from this software without specific prior written permission.
 *
 *   THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 *   "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 *   LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 *   A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 *   OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 *   SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 *   LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 *   DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 *   THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 *   (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 *   OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

#include <arpa/inet.h>
#include <errno.h>
#include <linux/if_packet.h>
#include <linux/if_ether.h>
#include <net/if.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/mman.h>
#include <sys/socket.h>
#include <sys/types.h>
#include <unistd.h>
#include <signal.h>
#include <time.h>
#include <string.h>
#include <limits.h>
#include <sys/ioctl.h>
#include <net/ethernet.h>
#include <poll.h>
#include <netinet/ether.h>
#include <netinet/ip.h>
#include <netinet/udp.h>
#include <sys/shm.h>

#define barrier() __asm__ __volatile__("": : :"memory")
#define smp_rmb()     barrier()
#define smp_wmb()     barrier()
#define likely(x)      __builtin_expect(!!(x), 1)
#define unlikely(x)    __builtin_expect(!!(x), 0)

#define BATCH_SIZE 32

#define FRAME_SIZE 2048
#define HEADER_HEADROOM 128 /* sizeof rte_mbuf */
#define DATA_HEADROOM 0 /* at least DATA_HEADROOM bytes */

#define SLEEP_STEP 10
#define MAX_SLEEP (1000000 / (SLEEP_STEP))

typedef char bool;
#define false 0
#define true 1
typedef uint64_t u64;
typedef uint32_t u32;
typedef uint8_t u8;

struct tp4_umem {
	size_t size;
	char *buffer;
	unsigned int frame_size;
	unsigned int frame_size_log2;
	unsigned int nframes;
	unsigned int header_headroom;
	unsigned int data_headroom;
	int mr_fd;
};

struct tp4_queue {
	struct tpacket4_queue tp4q;
	struct tp4_umem *umem;
	int sfd;
	char *interface_name;
	size_t outstanding_tx;
	bool start_of_pkt;
};

typedef int (*work_func)(struct tp4_queue *tp4q_rx,
			 struct tp4_queue *tp4q_tx,
			 struct tpacket4_desc *descs,
			 int recvd,
			 int error);

static inline int do_nothing(struct tp4_queue *tp4q_rx,
			     struct tp4_queue *tp4q_tx,
			     struct tpacket4_desc *descs,
			     int recvd,
			     int error);

#define LOG2(X) ((unsigned) (8*sizeof (unsigned long long) - __builtin_clzll((X)) - 1))

static unsigned long npkts;
static unsigned long start_time;
static uint64_t batch_sizes[BATCH_SIZE + 1] = {};
static unsigned pkt_buffers = 4 * 1024;
static work_func process_packets = do_nothing;
static unsigned int saved_buffers = 1;

/* For process synchronization */
static int shmid;
volatile unsigned int *sync_var;

/* to remove hex-dump completely for performance reasons */
#define HAS_HEX_DUMP 1
static int conf_dump_on;

static int conf_zero_copy_on;

static int conf_stats_on;

static int conf_poll_on;

static int conf_veth_on;

static int conf_l2fwd_on;

static int conf_jumbo_on;

static int conf_asym_on;

static int conf_shared_mem_on;

static unsigned int conf_reserve = 128; /* frame headroom in bytes */

static void *shmem;

static void usage(const char *bin)
{
	fprintf(stderr,
		"Usage: %s [-l to enable l2fwd] [-i interface name] [-z enable zero copy] [-s enable stats] [-p enable blocking mode] [-v veth mode] [-m shared packet buffer] [-j jumbo frames] [-a one ZC process and one without]"
#if HAS_HEX_DUMP
		" [-x enable packet dump]"
#endif
		"\n",
		bin);
	exit(EXIT_FAILURE);
}

#define lassert(expr)							\
	do {								\
		if (!(expr)) {						\
			fprintf(stderr, "%s:%s:%i: Assertion failed: " #expr ": errno: %d/\"%s\"\n", __FILE__, __func__, __LINE__, errno, strerror(errno)); \
			exit(EXIT_FAILURE);				\
		}							\
	} while(0)

static inline int tp4q_enqueue(struct tp4_queue *tp4q,
			       const struct tpacket4_desc *d,
			       unsigned int dcnt)
{
	struct tpacket4_queue *q = &tp4q->tp4q;
	unsigned int avail_idx = q->avail_idx;
	unsigned int i;
	int j;

	if (q->num_free < dcnt)
		return -ENOSPC;

	q->num_free -= dcnt;

	for (i = 0; i < dcnt; i++) {
		unsigned int idx = (avail_idx++) & (q->ring_size - 1);

		q->vring[idx].addr = d[i].addr;
		q->vring[idx].len = d[i].len;
		q->vring[idx].error = 0;
	}
	smp_wmb();

	for (j = dcnt - 1; j >= 0; j--) {
		unsigned int idx = (q->avail_idx + j) & (q->ring_size - 1);

		q->vring[idx].flags = d[j].flags | DESC_HW;
	}
	q->avail_idx += dcnt;

	return 0;
}

static inline int tp4q_dequeue(struct tp4_queue *tp4q,
			       struct tpacket4_desc *d,
			       int *error, int dcnt)
{
        struct tpacket4_queue *q = &tp4q->tp4q;
	int i, entries = 0;
	unsigned int idx, last_used_idx = q->last_used_idx;

	*error = 0;
	for (i = 0; i < dcnt; i++) {
		idx = (last_used_idx++) & (q->ring_size - 1);
		if (q->vring[idx].flags & DESC_HW)
			break;
		if (unlikely(q->vring[idx].error))
			*error = q->vring[idx].error;
		entries++;
	}
	q->num_free += entries;

	smp_rmb();

	for (i = 0; i < entries; i++) {
		idx = (q->last_used_idx++) & (q->ring_size - 1);
		d[i] = q->vring[idx];
	}

	return entries;
}

static inline bool tp4q_validate_header(struct tp4_queue *tp4q,
					struct tpacket4_hdr *hdr)
{
	unsigned int max_off = tp4q->umem->frame_size -
			       tp4q->umem->header_headroom;
	unsigned int min_off = TPACKET4_HDRLEN;

	if (hdr->data >= max_off || hdr->data < min_off ||
	    hdr->data_end > max_off || hdr->data_end < min_off ||
	    hdr->data_end < hdr->data) {
		return false;
	}

	return true;
}

static inline struct tpacket4_hdr *tp4q_get_header(struct tp4_queue *tp4q,
						   u64 addr)
{
	if (addr >= tp4q->umem->nframes)
		return false;

	return (struct tpacket4_hdr *)(tp4q->umem->buffer +
				       (addr << tp4q->umem->frame_size_log2) +
				       tp4q->umem->header_headroom);
}

static inline struct tpacket4_hdr *tp4q_get_validated_header(
	struct tp4_queue *tp4q, u64 addr)
{
	struct tpacket4_hdr *hdr;

	hdr = tp4q_get_header(tp4q, addr);
	if (!hdr || !tp4q_validate_header(tp4q, hdr))
		return NULL;

	return hdr;
}

static inline void tp4q_write_header(struct tp4_queue *tp4q,
				     struct tpacket4_hdr *hdr, u32 size)
{
	hdr->data = TPACKET4_HDRLEN + tp4q->umem->data_headroom;
	hdr->data_end = hdr->data + size;
}

static inline void *tp4q_get_data(struct tp4_queue *tp4q,
				  struct tpacket4_hdr *hdr)
{
	return (u8 *)hdr + TPACKET4_HDRLEN + tp4q->umem->data_headroom;
}

static inline unsigned int tp4q_max_data_size(struct tp4_queue *tp4q)
{
	return tp4q->umem->frame_size - tp4q->umem->header_headroom -
		TPACKET4_HDRLEN - tp4q->umem->data_headroom;
}

static inline bool tp4q_is_eop(struct tpacket4_desc *desc)
{
	return !(desc->flags & DESC_NEXT);
}

static inline int tp4q_first_frame(struct tp4_queue *tp4q,
				   struct tpacket4_desc *desc)
{
	if (!tp4q->start_of_pkt) {
		if (tp4q_is_eop(desc))
			tp4q->start_of_pkt = true;
		return 0;
	}
	else if (!tp4q_is_eop(desc))
		tp4q->start_of_pkt = false;

	return 1;
}


static unsigned long get_nsecs(void)
{
	struct timespec ts;

	clock_gettime(CLOCK_MONOTONIC, &ts);
	return ts.tv_sec * 1000000000UL + ts.tv_nsec;
}

static void swap_mac_addresses(void *data)
{
        struct ether_header *eth = (struct ether_header *)data;
        struct ether_addr *src_addr = (struct ether_addr *)&eth->ether_shost;
        struct ether_addr *dst_addr = (struct ether_addr *)&eth->ether_dhost;
        struct ether_addr tmp;

        tmp = *src_addr;
        *src_addr = *dst_addr;
        *dst_addr = tmp;
}

static void sigdie(int sig)
{
	unsigned long stop_time = get_nsecs();
	long dt = stop_time - start_time;
	int i;

	double pps = npkts * 1000000000. / dt;

	printf("Ran for %.2fs / %lupkts @ %.2fpps.\n", dt / 1000000000.,
	       npkts, pps);

	if (!conf_stats_on)
		exit(0);

	printf("\n");
	for (i = 0; i < BATCH_SIZE + 1; i++) {
		printf("%2d:%10lu\t", i, batch_sizes[i]);
		if (i % 4 == 3)
			printf("\n");
	}
	printf("\n");

	(void)sig;

	exit(0);
}

/* NB! We're not doing any cleanup what so ever. */

struct tp4_umem *alloc_and_register_buffers(size_t nbuffers)
{
	struct tp4_umem *umem;
	int fd;
	void *bufs;
	int ret;
	struct tpacket_memreg_req req = { .frame_size = FRAME_SIZE,
					  .header_headroom = HEADER_HEADROOM,
					  .data_headroom = DATA_HEADROOM };

	if (!shmem) {
		ret = posix_memalign((void **)&bufs, getpagesize(), nbuffers * req.frame_size);
		lassert(ret == 0);
	} else {
		bufs = shmem;
	}

	umem = malloc(sizeof(*umem));
	lassert(umem);
	fd = socket(PF_PACKET, SOCK_RAW, htons(ETH_P_ALL));
	lassert(fd > 0);
	req.addr = (unsigned long)bufs;
	req.len = nbuffers * req.frame_size;
	ret = setsockopt(fd, SOL_PACKET, PACKET_MEMREG, &req, sizeof(req));
	lassert(ret == 0);

	umem->frame_size = FRAME_SIZE;
	umem->frame_size_log2 = LOG2(FRAME_SIZE);
	umem->header_headroom = HEADER_HEADROOM;
	umem->data_headroom = ((HEADER_HEADROOM + TPACKET4_HDRLEN +
				DATA_HEADROOM + 63) & ~63) -
		(HEADER_HEADROOM + TPACKET4_HDRLEN);
	umem->buffer = bufs;
	umem->size = nbuffers * req.frame_size;
	umem->nframes = nbuffers;
	umem->mr_fd = fd;

	return umem;
}

#if HAS_HEX_DUMP
static void hex_dump(struct tpacket4_hdr *pkt, const char *prefix)
{
        int i = 0;
        const unsigned char *address = (unsigned char *)pkt + pkt->data;
        const unsigned char *line = address;
	size_t length = pkt->data_end - pkt->data;
	size_t line_size = BATCH_SIZE;
        unsigned char c;

	if (!conf_dump_on)
		return;

        printf("%s | ", prefix);
        while (length-- > 0) {
                printf("%02X ", *address++);
                if (!(++i % line_size) || (length == 0 && i % line_size)) {
                        if (length == 0) {
                                while (i++ % line_size)
                                        printf("__ ");
                        }
                        printf(" | ");  /* right close */
                        while (line < address) {
                                c = *line++;
                                printf("%c", (c < 33 || c == 255) ? 0x2E : c);
                        }
                        printf("\n");
                        if (length > 0)
                                printf("%s | ", prefix);
                }
        }
        printf("\n");
}
#else
#define hex_dump(...) do { } while(0)
#endif

static void kick_tx(int fd)
{
	int ret;

	ret = sendto(fd, NULL, 0, MSG_DONTWAIT, NULL, 0);
	if (ret >= 0 || errno == EAGAIN || errno == ENOBUFS)
		return;
	else
		lassert(0);
}

static inline void return_buffers(struct tp4_queue *tp4q_rx,
				  struct tpacket4_desc *descs,
				  unsigned int recvd,
				  int error)
{
	struct tpacket4_hdr *pkt;
	int ret;

	if (unlikely(error)) {
		printf("Error is returned. %s\n", strerror(error));
	} else if (conf_dump_on) {
		pkt = tp4q_get_validated_header(tp4q_rx, descs[0].addr);
		if (pkt)
			hex_dump(pkt, "Rx:");
		else
			printf("Packet has bad header.\n");
	}

	ret = tp4q_enqueue(tp4q_rx, descs, recvd);
	lassert(ret == 0);
}


static inline void complete_tx(struct tp4_queue *tp4q_rx,
			       struct tp4_queue *tp4q_tx,
			       struct tpacket4_desc *descs)
{
	unsigned int recvd;
	size_t ndescs;
	int error;
	int ret;

	if (!tp4q_tx->outstanding_tx)
		return;

	ndescs = (tp4q_tx->outstanding_tx > BATCH_SIZE) ? BATCH_SIZE :
		tp4q_tx->outstanding_tx;

	/* re-add completed Tx buffers */
	recvd = tp4q_dequeue(tp4q_tx, descs, &error, ndescs);
	if (recvd > 0) {
		unsigned int i;

		if (likely(!error)) {
			/* Fast path */
			ret = tp4q_enqueue(tp4q_rx, descs, recvd);
			lassert(ret == 0);
			tp4q_tx->outstanding_tx -= recvd;
		} else {
			/* Slow path */
			for (i = 0; i < recvd; i++) {
				if (descs[i].error) {
					printf("%s: %s. Retrying sending packet. recvd %u.\n",
					      tp4q_rx->interface_name,
					      strerror(descs[i].error), recvd);
					ret = tp4q_enqueue(tp4q_tx, &descs[i], 1);
					lassert(ret == 0);
				} else {
					ret = tp4q_enqueue(tp4q_rx, &descs[i], 1);
					lassert(ret == 0);
					tp4q_tx->outstanding_tx--;
				}
			}

			kick_tx(tp4q_tx->sfd);
		}
	}
}

static inline int do_l2fwd(struct tp4_queue *tp4q_rx,
			   struct tp4_queue *tp4q_tx,
			   struct tpacket4_desc *descs,
			   int recvd,
			   int error)
{
	int ret;
	int i;

	for (i = 0; i < recvd; i++) {
		struct tpacket4_hdr *hdr =
			tp4q_get_header(tp4q_rx, descs[i].addr);

		if (!tp4q_first_frame(tp4q_rx, &descs[i]))
			continue;

		if (likely(!descs[i].error)) {
			hex_dump(hdr, "Rx: ");
			swap_mac_addresses(tp4q_get_data(tp4q_rx, hdr));
			hex_dump(hdr, "Tx: ");

			if (error) {
				ret = tp4q_enqueue(tp4q_tx, &descs[i], 1);
				lassert(ret == 0);
				tp4q_tx->outstanding_tx++;
			}
		}
		else {
			printf("%s: Packet has bad header or descriptor\n",
			       tp4q_tx->interface_name);
			ret = tp4q_enqueue(tp4q_rx, &descs[i], 1);
			lassert(ret == 0);
		}
	}

	return error ? 1 : 0;
}

static inline int do_nothing(struct tp4_queue *tp4q_rx,
			     struct tp4_queue *tp4q_tx,
			     struct tpacket4_desc *descs,
			     int recvd,
			     int error)
{
	(void)(tp4q_rx);
	(void)(tp4q_tx);
	(void)(descs);
	(void)(recvd);
	(void)(error);

	return 0;
}

static inline void send_packets(struct tp4_queue *tp4q_tx,
				struct tpacket4_desc *descs,
				int recvd)
{
	int ret;

	ret = tp4q_enqueue(tp4q_tx, descs, recvd);
	if (ret == 0) {
		tp4q_tx->outstanding_tx += recvd;
		kick_tx(tp4q_tx->sfd);
	}
}

static void configure_tp4(struct tp4_queue **rx,
			  struct tp4_queue **tx,
			  char *interface_name)
{
	struct tp4_queue *tp4q_rx, *tp4q_tx;
	struct tpacket4_queue *rxq, *txq;
	int ret, tpver = TPACKET_V4;
	struct tpacket_req4 req;
	struct tp4_umem *umem;
        struct sockaddr_ll ll;
	unsigned int i;
	void *rxring;
	int sfd;

	ret = if_nametoindex(interface_name);
	if (!ret) {
		printf("Error: interface %s does not exist.\n",
		       interface_name);
		exit(0);
	}

	/* create PF_PACKET socket */
	sfd = socket(PF_PACKET, SOCK_RAW, htons(ETH_P_ALL));
	lassert(sfd >= 0);
	ret = setsockopt(sfd, SOL_PACKET, PACKET_VERSION, &tpver,
			 sizeof(tpver));
	lassert(ret == 0);

	if (conf_reserve) {
		ret = setsockopt(sfd, SOL_PACKET, PACKET_RESERVE,
				&conf_reserve, sizeof(conf_reserve));
		lassert(ret == 0);
	}

	*rx = calloc(1, sizeof(*tp4q_rx));
	lassert(*rx);
	tp4q_rx = *rx;
	*tx = calloc(1, sizeof(*tp4q_tx));
	lassert(*tx);
	tp4q_tx = *tx;
	umem = alloc_and_register_buffers(pkt_buffers);
	lassert(umem);

	tp4q_rx->umem = umem;
	tp4q_tx->umem = umem;
	tp4q_rx->sfd = sfd;
	tp4q_tx->sfd = sfd;
	tp4q_rx->start_of_pkt = true;
	tp4q_tx->start_of_pkt = true;
	tp4q_rx->interface_name = interface_name;
	tp4q_tx->interface_name = interface_name;

	req.mr_fd = umem->mr_fd;
	req.desc_nr = 2048;
	ret = setsockopt(sfd, SOL_PACKET, PACKET_RX_RING, &req, sizeof(req));
	lassert(ret == 0);
	ret = setsockopt(sfd, SOL_PACKET, PACKET_TX_RING, &req, sizeof(req));
	lassert(ret == 0);

	/* NB! txring is, as in V2/V3, mmapped in the same mmap
	 * call. */
	rxring = mmap(0, 2 * req.desc_nr * sizeof(struct tpacket4_desc),
		      PROT_READ | PROT_WRITE,
		      MAP_SHARED | MAP_LOCKED | MAP_POPULATE, sfd, 0);
	lassert(rxring != MAP_FAILED);

	rxq = &tp4q_rx->tp4q;
	rxq->vring = rxring;
	rxq->num_free = req.desc_nr;
	rxq->ring_size = req.desc_nr;

	/* TX ring starts right after the RX ring ends,
	   halfways into the buffer */
	txq = &tp4q_tx->tp4q;
	txq->vring = &rxq->vring[req.desc_nr];
	txq->num_free = req.desc_nr;
	txq->ring_size = req.desc_nr;

	ll.sll_family = PF_PACKET;
	ll.sll_protocol = htons(ETH_P_ALL);
	ll.sll_ifindex = if_nametoindex(interface_name);
	ll.sll_hatype = 0;
	ll.sll_pkttype = 0;
	ll.sll_halen = 0;

	printf("Using interface %s\n", interface_name);
	ret = bind(sfd, (struct sockaddr *)&ll, sizeof(ll));
	lassert(ret == 0);

	if (conf_zero_copy_on || (conf_asym_on &&
				  !strcmp(interface_name, "vm1"))) {
		ret = setsockopt(sfd, SOL_PACKET, PACKET_ZEROCOPY, NULL, 0);
		lassert(ret == 0);
	}

	/* Gift some buffers to the kernel */
	for (i = saved_buffers; i < tp4q_rx->tp4q.ring_size; i++) {
		struct tpacket4_desc desc = { .addr = i};
		
		ret = tp4q_enqueue(tp4q_rx, &desc, 1);
		lassert(ret == 0);
	}
}

static void syscall_poll_loop(struct tp4_queue *tp4q_rx,
			      struct tp4_queue *tp4q_tx)
{
	struct tpacket4_desc descs[BATCH_SIZE];
	unsigned int recvd = 0;
	struct pollfd fds[2];
	int nfds = 1;
	int timeout;
	int error;
	int ret;

	memset(fds, 0 , sizeof(fds));
	fds[0].fd = tp4q_tx->sfd;
	fds[0].events = POLLIN;

	timeout = 1000; /* 1sn */

	for (;;) {
		int packets_sent;

		/* re-add completed Tx buffers */
		complete_tx(tp4q_rx, tp4q_tx, descs);

		/*** RX ***/
		fds[0].events = POLLIN;
		ret = poll(fds, nfds, timeout);
		if (ret <= 0)
			continue;

		if (fds[0].fd != tp4q_tx->sfd || !(fds[0].revents & POLLIN))
			continue;

		recvd = tp4q_dequeue(tp4q_rx, descs, &error, BATCH_SIZE);
		batch_sizes[recvd]++;
		npkts += recvd;

		if (recvd == 0)
			continue;

		packets_sent = process_packets(tp4q_rx, tp4q_tx, descs, recvd,
					       error);

		if (likely(!packets_sent) && conf_l2fwd_on) {
			for (;;) {
				fds[0].events = POLLOUT;
				ret = poll(fds, nfds, timeout);
				if (ret <= 0) {
					printf("Waiting for sending...\n");
					continue;
				}

				if (fds[0].fd != tp4q_tx->sfd ||
				    !(fds[0].revents & POLLOUT))
					continue;

				ret = tp4q_enqueue(tp4q_tx, descs, recvd);
				if (!ret) {
					tp4q_tx->outstanding_tx += recvd;
					break;
				}
			}

			kick_tx(tp4q_tx->sfd);

		} else if (likely(!packets_sent)) {
			return_buffers(tp4q_rx, descs, recvd, error);
		}
	}
}

static void direct_poll_loop(struct tp4_queue *tp4q_rx,
			     struct tp4_queue *tp4q_tx)
{

	for (;;) {
		struct tpacket4_desc descs[BATCH_SIZE];
		unsigned int recvd;
		int packets_sent;
		int error;

		for (;;) {
			complete_tx(tp4q_rx, tp4q_tx, descs);

			recvd = tp4q_dequeue(tp4q_rx, descs, &error,
					     BATCH_SIZE);
			batch_sizes[recvd]++;
			if (recvd > 0)
				break;
		}

		npkts += recvd;
		packets_sent = process_packets(tp4q_rx, tp4q_tx, descs, recvd,
					       error);
		if (likely(!packets_sent)) {
			if (conf_l2fwd_on)
				send_packets(tp4q_tx, descs, recvd);
			else
				return_buffers(tp4q_rx, descs, recvd, error);
		}
	}
}

static void run_benchmark(char *interface_name)
{
	struct tp4_queue *tp4q_rx, *tp4q_tx;
	unsigned int i;
	int ret;

	configure_tp4(&tp4q_rx, &tp4q_tx, interface_name);

	/* Notify parent that interface configuration completed */
	if (!strcmp(interface_name, "vm2") && sync_var)
		*sync_var = 1;

	signal(SIGINT, sigdie);

	/* TODO. Until we have a watchdog in
	 * place we need this for FVL. --Björn
	 * Now also used to generate the ping-pong packets for the
	 * veth test :-). --Magnus
	 */
	if (!conf_veth_on || !strcmp(interface_name, "vm1")) {
		for (i = 0; i < saved_buffers; i++) {
			struct tpacket4_desc d = { .addr = i,
						   .len = 64,
						   .flags = 0};
			struct tpacket4_hdr *hdr;

			hdr = tp4q_get_header(tp4q_tx, d.addr);
			lassert(hdr);

			if (conf_jumbo_on) {
				if (i != saved_buffers - 1) {
					d.flags = DESC_NEXT;
					d.len = tp4q_max_data_size(tp4q_tx) - 256;
				}
			}

			tp4q_write_header(tp4q_tx, hdr, d.len);
			ret = tp4q_enqueue(tp4q_tx, &d, 1);
			lassert(ret == 0);
			tp4q_tx->outstanding_tx++;
		}
		ret = sendto(tp4q_tx->sfd, NULL, 0, MSG_DONTWAIT, NULL, 0);
		lassert(ret != -1);
	}

	start_time = get_nsecs();

	if (conf_poll_on)
		syscall_poll_loop(tp4q_rx, tp4q_tx);
	else
		direct_poll_loop(tp4q_rx, tp4q_tx);

	/* Will never get here. */
}

int main(int argc, char **argv)
{
	int ret, opt;
	char interface_name[64] = "ens6f0";

	while ((opt = getopt(argc, argv, "li:xzspv:maj")) != -1) {
		switch (opt) {
		case 'l':
			conf_l2fwd_on = 1;
			break;
		case 'i':
			ret = if_nametoindex(optarg);
			if (!ret) {
				printf("Error: interface %s does not exist.\n",
				       optarg);
				exit(0);
			}
			strncpy(interface_name, optarg,
				sizeof(interface_name));
			break;
		case 'x': /* hex-dump */
			conf_dump_on = 1;
			break;
		case 'z': /* zero-copy */
			conf_zero_copy_on = 1;
			break;
		case 's': /* stats */
			conf_stats_on = 1;
			break;
		case 'p': /* blocking mode */
			conf_poll_on = 1;
			break;
		case 'j': /* jumbo frames */
			conf_jumbo_on = 1;
			break;
		case 'a': /* Asymetric operation. One ZC process and one
			     without */
			conf_asym_on = 1;
			break;
		case 'v': /* veth mode */
			conf_veth_on = 1;
			conf_l2fwd_on = 1;
			saved_buffers = atoi(optarg);
			if (saved_buffers == 0)
				saved_buffers = 1;
			break;
		case 'm': /* shared memory mode */
			conf_shared_mem_on = 1;
			break;
		default:
			usage(argv[0]);
		}
	}

	if (conf_l2fwd_on)
		process_packets = do_l2fwd;

	if (conf_jumbo_on && saved_buffers <= 1)
		saved_buffers = 2;

	if (conf_asym_on && conf_zero_copy_on) {
		printf("ERROR: -a and -z are mutually exclusive.\n");
		exit(0);
	}

	if (conf_asym_on && !conf_veth_on) {
		printf("ERROR: -a is only supported with veth (-v).\n");
		exit(0);
	}

	if (conf_veth_on) {

		if (conf_shared_mem_on) {
			shmem = mmap(NULL, pkt_buffers * FRAME_SIZE,
				     PROT_READ | PROT_WRITE,
				     MAP_ANONYMOUS | MAP_SHARED, 0, 0);
			if (shmem == MAP_FAILED) {
				printf("ERROR: allocating shared memory failed\n");
				exit(0);
			}
		}

		shmid = shmget(14082017, sizeof(unsigned int), IPC_CREAT | 666);
		sync_var = shmat(shmid, 0, 0);
		*sync_var = 0;

		conf_l2fwd_on = 1;
		if (fork() == 0) {
			run_benchmark("vm2");
		} else {
			unsigned int i;

			/* Wait for child */
			for (i = 0; *sync_var == 0 && i < MAX_SLEEP; i++)
				usleep(SLEEP_STEP);
			if (i >= MAX_SLEEP)
				sigdie(0);
			printf("vm1 slept for %u us.\n", i * SLEEP_STEP);

			run_benchmark("vm1");
		}
	} else {
		run_benchmark(interface_name);
	}

	/* Will never get here */
}
