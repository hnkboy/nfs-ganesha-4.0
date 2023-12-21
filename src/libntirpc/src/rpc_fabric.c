/*
 * Copyright (c) 2012-2014 CEA
 * contributeur : Dominique Martinet <dominique.martinet@cea.fr>
 * contributeur : William Allen Simpson <bill@cohortfs.com>
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 * - Redistributions of source code must retain the above copyright notice,
 *   this list of conditions and the following disclaimer.
 * - Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 * - Neither the name of Sun Microsystems, Inc. nor the names of its
 *   contributors may be used to endorse or promote products derived
 *   from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE
 * LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
 * CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
 * SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
 * INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
 * CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 */

/**
 * \file    rpc_rdma.c
 * \brief   rdma helper
 *
 * This was (very) loosely based on the Mooshika library, which in turn
 * was a mix of diod, rping (librdmacm/examples), and Linux kernel's
 * net/9p/trans_rdma.c (dual BSD/GPL license). No vestiges remain.
 */

#if HAVE_CONFIG_H
#  include "config.h"
#endif

#include <stdio.h>	//printf
#include <limits.h>	//INT_MAX
#include <sys/socket.h> //sockaddr
#include <sys/un.h>     //sockaddr_un
#include <pthread.h>	//pthread_* (think it's included by another one)
#include <semaphore.h>  //sem_* (is it a good idea to mix sem and pthread_cond/mutex?)
#include <arpa/inet.h>  //inet_ntop
#include <netinet/in.h> //sock_addr_in
#include <unistd.h>	//fcntl
#include <fcntl.h>	//fcntl
#include <sys/epoll.h>
#include <urcu-bp.h>

#define EPOLL_SIZE (10)
/*^ expected number of fd, must be > 0 */
#define EPOLL_EVENTS (16)
/*^ maximum number of events per poll */
#define EPOLL_WAIT_MS (1000)
/*^ ms check for rpc_rdma_state.run_count (was 100) */
#define IBV_POLL_EVENTS (16)
/*^ maximum number of events per poll */
#define NSEC_IN_SEC (1000*1000*1000)

#include "misc/portable.h"
#include <rdma/rdma_cma.h>
#include <rpc/types.h>
#include <rpc/xdr.h>
#include <rpc/xdr_ioq.h>
#include <rpc/rpc.h>

#include "misc/abstract_atomic.h"
#include "rpc_rdma.h"
#include "svc_internal.h"
#include "rpc_com.h"
#include "misc/city.h"
#include "svc_internal.h"
#include "svc_xprt.h"
#include "rpc_rdma.h"
#include <rpc/svc_rqst.h>
#include <rpc/svc_auth.h>



#include <rdma/fi_errno.h>
#include <rdma/fi_cm.h>
#include <rdma/fi_rma.h>
#include <assert.h>

char *dst_addr = NULL;

struct fid_domain *domain;
static struct fi_eq_attr eq_attr;
static struct fi_cq_attr cq_attr;
struct fid_cq *txcq, *rxcq;

struct fi_info *hints, *info;
static struct fi_info *fi;
static struct fi_info *fi_pep;

struct fid_fabric *fabric = NULL;
struct fid_domain *domain = NULL;
struct fid_ep *ep = NULL; /*一个是ep，一个eq*/
struct fid_pep *pep = NULL;
static struct fid_eq *eq;

char **tx_mr_bufs = NULL, **rx_mr_bufs = NULL;
size_t buf_size, tx_buf_size, rx_buf_size;
size_t tx_size, rx_size, tx_mr_size, rx_mr_size;
fi_addr_t remote_fi_addr = FI_ADDR_UNSPEC;
char *buf = NULL, *tx_buf, *rx_buf;

struct fid_mr no_mr;
static struct fid_mr *mr;
void *mr_desc = NULL;

struct rpc_rdma_cbc *global_cbc;
struct poolq_entry *pentry ;
 struct xdr_ioq_uv *global_ioq;
RDMAXPRT *global_xd;

#define BUF_SIZE 64
char g_rx_buf[BUF_SIZE];


#define OFI_MR_BASIC_MAP (FI_MR_ALLOCATED | FI_MR_PROV_KEY | FI_MR_VIRT_ADDR)

#define MR_KEY 0xC0DE

#define MSG_MR_ACCESS (FI_SEND | FI_RECV)
#define RMA_MR_ACCESS (FI_READ | FI_WRITE | FI_REMOTE_READ | FI_REMOTE_WRITE)

#define FT_ERR(fmt, ...) printf(fmt, ##__VA_ARGS__)
#define FT_CQ_ERR(cq, entry, buf, len)					\
	FT_ERR("cq_readerr %d (%s), provider errno: %d (%s)",		\
		entry.err, fi_strerror(entry.err),			\
		entry.prov_errno, fi_cq_strerror(cq, entry.prov_errno,	\
						 entry.err_data,	\
						 buf, len))		\


#define FT_PRINTERR(call, retv)						\
	do {								\
		int saved_errno = errno;				\
		fprintf(stderr, call "(): %s:%d, ret=%d (%s)\n",	\
			__FILE__, __LINE__, (int) (retv),		\
			fi_strerror((int) -(retv)));			\
		errno = saved_errno;					\
	} while (0)

#define FA_PRINT(fmt, ...)						\
	__warnx(TIRPC_DEBUG_FLAG_ERROR, \
	"%s() NFS/FABRIC  "fmt"\n", __func__, ##__VA_ARGS__);

#include <rdma/fi_errno.h>

static void print_cq_error(struct fid_cq* cq) {
	int ret;
	struct fi_cq_err_entry cq_err;
	ret = fi_cq_readerr(cq, &cq_err, 0);
	if (ret < 0) {
		FT_PRINTERR("fi_cq_readerr", ret);
	} else {
		FT_CQ_ERR(cq, cq_err, NULL, 0);
	}
}







struct xp_ops rpc_fabric_ops;


/**
 * rpc_rdma_setup_cbq
 */
static int
rpc_fabric_setup_cbq(struct poolq_head *ioqh, u_int depth, u_int sge)
{
	struct rpc_rdma_cbc *cbc;

	if (ioqh->qsize) {
		__warnx(TIRPC_DEBUG_FLAG_ERROR,
			"%s() contexts already allocated",
			__func__);
		return EINVAL;
	}
	ioqh->qsize = sizeof(struct rpc_rdma_cbc)
		    + sizeof(struct ibv_sge) * sge;
	TAILQ_INIT(&ioqh->qh);

	/* individual entries is less efficient than big array -- but uses
	 * "standard" IOQ operations, xdr_ioq_destroy_pool(), and
	 * debugging memory bounds checking of trailing ibv_sge array.
	 */
	while (depth--) {
		cbc = mem_zalloc(ioqh->qsize);

		xdr_ioq_setup(&cbc->workq);
		xdr_ioq_setup(&cbc->holdq);

		cbc->workq.ioq_uv.uvq_fetch =
		cbc->holdq.ioq_uv.uvq_fetch = xdr_ioq_uv_fetch_nothing;
		cbc->workq.xdrs[0].x_ops =
		cbc->holdq.xdrs[0].x_ops = &xdr_ioq_ops;
		cbc->workq.xdrs[0].x_op =
		cbc->holdq.xdrs[0].x_op = XDR_FREE; /* catch setup errors */

		cbc->workq.ioq_pool = ioqh;
		//cbc->wpe.fun = rpc_rdma_worker_callback;

		(ioqh->qcount)++;
		TAILQ_INSERT_TAIL(&ioqh->qh, &cbc->workq.ioq_s, q);
	}
	return 0;
}


static int post_recv(RDMAXPRT *xd)
{
	int ret;

	struct poolq_entry *have =
		xdr_ioq_uv_fetch(&xd->sm_dr.ioq, &xd->cbqh,
				 "callq context", 1, IOQ_FLAG_NONE);
	struct rpc_rdma_cbc *cbc = (struct rpc_rdma_cbc *)(_IOQ(have));

	have = xdr_ioq_uv_fetch(&cbc->workq, &xd->inbufs.uvqh,
				"callq buffer", 1, IOQ_FLAG_NONE);
	
	/* input positions */
	IOQ_(have)->v.vio_head = IOQ_(have)->v.vio_base;
	IOQ_(have)->v.vio_tail = IOQ_(have)->v.vio_wrap;
	IOQ_(have)->v.vio_wrap = (char *)IOQ_(have)->v.vio_base
			       + xd->sm_dr.recvsz;

	cbc->workq.xdrs[0].x_lib[1] =
	cbc->holdq.xdrs[0].x_lib[1] = xd;
	pentry = have;
	global_cbc = cbc;
	global_ioq = IOQ_(have);
	global_xd = xd;
	__warnx(TIRPC_DEBUG_FLAG_ERROR,
			"%s() NFS/FABRIC cbc %p, base %p.", __func__, cbc, IOQ_(have)->v.vio_head);
	do {
		ret = fi_recv(ep, IOQ_(have)->v.vio_head,
			xd->sm_dr.recvsz, mr, remote_fi_addr, cbc);
		if (ret && ret != -FI_EAGAIN) {
			FA_PRINT("error fi_recv %d\n", ret);
			return ret;
		}
		if (ret == -FI_EAGAIN){
			(void) fi_cq_read(rxcq, NULL, 0);
			FA_PRINT("error fi_recv %d\n", ret);
		}
	} while (ret);
	return 0;
}

static int wait_recvcq(void)
{
	struct fi_cq_err_entry comp;
	int ret;

	do {
		ret = fi_cq_read(rxcq, &comp, 1);
		if (ret < 0 && ret != -FI_EAGAIN) {
			if (ret == -FI_EAVAIL) {
				print_cq_error(rxcq);
			}
			printf("error reading cq (%d), %s\n", ret, fi_strerror(ret));
			return ret;
		}
	} while (ret != 1);

	if (comp.flags & FI_RECV)
		printf("I received a message!\n");
	else if (comp.flags & FI_SEND)
		printf("My message got sent!\n");
	ret = comp.len;
	global_cbc = comp.op_context;
	__warnx(TIRPC_DEBUG_FLAG_ERROR,
			"%s() NFS/FABRIC comp.op_context %p.", __func__, comp.op_context);
	return ret;
}

#if 0
/* Post a send buffer. This call does not ensure a message has been sent, just that
 * a buffer has been submitted to OFI to be sent. Unlike a receive buffer, a send
 * needs a valid fi_addr as input to tell the provider where to send the message.
 * Similar to the receive buffer posting porcess, when posting a send buffer, if the
 * provider is not ready to process messages, it may return -FI_EAGAIN. This does not
 * indicate an error, but rather that the application should try again later. Just like
 * the receive, we drive progress with fi_cq_read if this is the case.
 */
static int post_send(void *buf, ssize_t size)
{
        int ret;

        do {
                ret = fi_send(ep, buf, size, NULL, remote_fi_addr, NULL);
                if (ret && ret != -FI_EAGAIN) {
                        printf("error posting send buffer (%d)\n", ret);
                        return ret;
                }
                if (ret == -FI_EAGAIN)
                        (void) fi_cq_read(txcq, NULL, 0);
        } while (ret);

        return 0;
}
#endif

static int wait_sendcq(void)
{
	struct fi_cq_err_entry comp;
	int ret;

	do {
		ret = fi_cq_read(txcq, &comp, 1);
		if (ret < 0 && ret != -FI_EAGAIN) {
			if (ret == -FI_EAVAIL) {
				print_cq_error(txcq);
			}
			printf("error reading cq (%d), %s\n", ret, fi_strerror(ret));
			return ret;
		}
	} while (ret != 1);

	if (comp.flags & FI_RECV)
		printf("I received a message!\n");
	else if (comp.flags & FI_SEND)
		printf("My message got sent!\n");
	ret = comp.len;
	//__warnx(TIRPC_DEBUG_FLAG_ERROR,
	//		"%s() NFS/FABRIC cq_read %p, base %p.", __func__, cbc, IOQ_(have)->v.vio_head);
	return ret;
}
static void printf_finfo(struct fi_info *info, char *args)
{
	__warnx(TIRPC_DEBUG_FLAG_ERROR,
	"%s() NFS/FABRIC\n %s-1 info: \ncaps:0x%x;\nmode:0x%x;", 
	__func__, 
	args,
	info->caps,
	info->mode);
	__warnx(TIRPC_DEBUG_FLAG_ERROR,
	"%s() NFS/FABRIC\n %s-2 info: txattr: \ncaps:0x%x;\nmode:0x%x;\nop_flags:0x%x;\nsize:0x%x;\niov_limit:0x%x;\nrma_iov_limit:0x%x;\ntclass:0x%x", 
	__func__, 
	args,
	info->tx_attr->caps,
	info->tx_attr->mode,
	info->tx_attr->op_flags,
	info->tx_attr->size, 
	info->tx_attr->iov_limit, 
	info->tx_attr->rma_iov_limit,
	info->tx_attr->tclass);
	__warnx(TIRPC_DEBUG_FLAG_ERROR,
	"%s() NFS/FABRIC\n %s-3 info: rxattr: \ncaps:0x%x;\nmode:0x%x;\nop_flags:0x%x;\nsize:0x%x;\niov_limit:0x%x;\nrma_iov_limit:NA;\ntclass:NA", 
	__func__, 
	args,
	info->rx_attr->caps,
	info->rx_attr->mode,
	info->rx_attr->op_flags,
	info->rx_attr->size, 
	info->rx_attr->iov_limit);
	return;
}

static int start_server(RDMAXPRT *xd)
{
	int ret = -1;
	//char *service_port = "9228";

	char *service_port = xd->xa->port;
	ret = fi_getinfo(FI_VERSION(1,20), NULL, service_port, FI_SOURCE, hints, &fi_pep);
	if (ret) {
		printf("fi_getinfo error (%d)\n", ret);
		return ret;
	}

	printf_finfo(hints, "init_hints");
	printf_finfo(hints, "get_hints");
	

	ret = fi_fabric(fi_pep->fabric_attr, &fabric, NULL); // 打开fabric, 初始化任何资源前需要打开fabric
	if (ret) {
		printf("fi_fabric error (%d)\n", ret);
		return ret;
	}
    ret = fi_eq_open(fabric, &eq_attr, &eq, NULL);       // 打开事件队列EQ, 一般用于建连, 收发数据产生的事件
    if (ret) {
		printf("fi_eq_open: %d\n", ret);
		return ret;
    }
    ret = fi_passive_ep(fabric, fi_pep, &pep, NULL);     // 打开被动端点, 常用与服务端监听端口, 支持多个客户端domain连接进来
    if (ret) {
        printf("fi_passive_ep: %d\n", ret);
        return ret;
    }
    ret = fi_pep_bind(pep, &eq->fid, 0);                 // 为端点绑定事件队列
    if (ret) {
        printf("fi_pep_bind %d", ret);
        return ret;
    }

    ret = fi_listen(pep);                                // 监听端点, 等待客户端连接请求
    if (ret) {
        printf("fi_listen %d", ret);
        return ret;
    }
    return 0;
}
static int server_connect(RDMAXPRT *xd)
{
	ssize_t rd;
	int ret;
	struct fi_eq_cm_entry entry;
	uint32_t event;

	__warnx(TIRPC_DEBUG_FLAG_ERROR,
			"%s() NFS/FABRIC eq sread . wait.", __func__);
	rd = fi_eq_sread(eq, &event, &entry, sizeof(entry), -1, 0); // 等待读取客户端触发的服务端事件, 读取事件, 推动进展(驱动程序运转)
	if (rd != sizeof(entry)) {
		ret = (int) rd;
		printf("fi_eq_sread: %d", ret);
		if (ret)
			goto err;
	}
	fi = entry.info;                            // info赋值到fi,后续操作的fi都是这个连接后的
	printf_finfo(fi, "get_client_hints");

	printf("fi_eq_sread: %d\n", ret);
	ret = fi_domain(fabric, fi, &domain, NULL); // domain域用于将资源分组, 可基于域来做管理
	if (ret) {
		printf("fi_domain: %d\n", ret);
		return ret;
	}

	ret = fi_domain_bind(domain, &eq->fid, 0);
	if (ret) {
		printf("fi_domain_bind: %d\n", ret);
		return ret;
	}

	cq_attr.size = 384;
	cq_attr.format = FI_CQ_FORMAT_CONTEXT;
	ret = fi_cq_open(domain, &cq_attr, &txcq, &txcq);
	if (ret) {
		printf("fi_cq_open error (%d)\n", ret);
		return ret;
	}
	ret = fi_cq_open(domain, &cq_attr, &rxcq, &rxcq);
	if (ret) {
		printf("fi_cq_open error (%d)\n", ret);
		return ret;
	}

	ret = fi_endpoint(domain, fi, &ep, NULL); // 用于客户端, 主动端点, 发起建连，fi是sread之后赋值的
	if (ret) {
		printf("fi_endpoint: %d\n", ret);
		return ret;
	}

	ret = fi_ep_bind((ep), &(eq)->fid, 0);
	if (ret) {
		printf("fi_ep_bind: %d\n", ret);
		return ret;
	}

	ret = fi_ep_bind(ep, &txcq->fid, FI_SEND);
	if (ret) {
		printf("fi_ep_bind cq error (%d)\n", ret);
		return ret;
	}
	ret = fi_ep_bind(ep, &rxcq->fid, FI_RECV);
	if (ret) {
		printf("fi_ep_bind cq error (%d)\n", ret);
		return ret;
	}
	ret = fi_enable(ep);
	if (ret) {
		printf("fi_enable: %d", ret);
		return ret;
	}


	//mr = &no_mr;
	ret = fi_mr_reg(domain, xd->buffer_aligned, xd->buffer_total, FI_RECV | FI_SEND,
			0, MR_KEY, 0, &mr, NULL);
	if (ret) {
		__warnx(TIRPC_DEBUG_FLAG_ERROR,
				"%s() NFS/FABRIC fi_mr_reg faild ret:%d.", __func__, ret);
		return ret;
	}
	mr_desc = fi_mr_desc(mr);


	//ret = post_recv(xd->buffer_aligned, xd->sm_dr.sendsz);
	//FA_PRINT("post recv success %d ", ret);

	ret = fi_accept(ep, NULL, 0);
	if (ret) {
		printf("fi_accept: %d\n", ret);
		return ret;
	}
	rd = fi_eq_sread(eq, &event, &entry, sizeof(entry), -1, 0);
	if (rd != sizeof(entry)) {
		ret = (int) rd;
		printf("fi_eq_read: %d\n", ret);
		return ret;
	}
	__warnx(TIRPC_DEBUG_FLAG_ERROR,
			"%s() NFS/FABRIC NFS/FABRIC accept success . wait.", __func__);
	return 0;
err:
    if (fi)
        fi_reject(pep, fi->handle, NULL, 0);
    return ret;
}

/*
 * initializes a stream descriptor for a memory buffer.
 *
 * credits is the number of buffers used
 */
int
xdr_fabric_create(RDMAXPRT *xd)
{
	uint8_t *b;
	int rc;
#if 0
	if (!xd->pd || !xd->pd->pd) {
		__warnx(TIRPC_DEBUG_FLAG_ERROR,
			"%s() %p[%u] missing Protection Domain",
			__func__, xd, xd->state);
		return ENODEV;
	}
#endif

	/* pre-allocated buffer_total:
	 * the number of credits is irrelevant here.
	 * instead, allocate buffers to match the read/write contexts.
	 * more than one buffer can be chained to one ioq_uv head,
	 * but never need more ioq_uv heads than buffers.
	 */
	xd->buffer_total = xd->sm_dr.recvsz * xd->xa->rq_depth
			 + xd->sm_dr.sendsz * xd->xa->sq_depth;

	xd->buffer_aligned = mem_aligned(xd->sm_dr.pagesz, xd->buffer_total);



#if 0
	/* register it in two chunks for read and write??? */
	xd->mr = ibv_reg_mr(xd->pd->pd, xd->buffer_aligned, xd->buffer_total,
			    IBV_ACCESS_LOCAL_WRITE |
			    IBV_ACCESS_REMOTE_WRITE |
			    IBV_ACCESS_REMOTE_READ);
#endif

	poolq_head_setup(&xd->inbufs.uvqh);
	xd->inbufs.min_bsize = xd->sm_dr.pagesz;
	xd->inbufs.max_bsize = xd->sm_dr.recvsz;

	poolq_head_setup(&xd->outbufs.uvqh);
	xd->outbufs.min_bsize = xd->sm_dr.pagesz;
	xd->outbufs.max_bsize = xd->sm_dr.sendsz;

	/* Each pre-allocated buffer has a corresponding xdr_ioq_uv,
	 * stored on the pool queues.
	 */
	b = xd->buffer_aligned;
	/* 内存分配到各个iov*/
	for (xd->inbufs.uvqh.qcount = 0;
	     xd->inbufs.uvqh.qcount < xd->xa->rq_depth;
	     xd->inbufs.uvqh.qcount++) {
		struct xdr_ioq_uv *data = xdr_ioq_uv_create(0, UIO_FLAG_BUFQ);

		data->v.vio_base =
		data->v.vio_head =
		data->v.vio_tail = b;
		data->v.vio_wrap = (char *)b + xd->sm_dr.recvsz;
		data->u.uio_p1 = &xd->inbufs.uvqh;
		data->u.uio_p2 = xd->mr;
		TAILQ_INSERT_TAIL(&xd->inbufs.uvqh.qh, &data->uvq, q);

		b += xd->sm_dr.recvsz;
	}

	for (xd->outbufs.uvqh.qcount = 0;
	     xd->outbufs.uvqh.qcount < xd->xa->sq_depth;
	     xd->outbufs.uvqh.qcount++) {
		struct xdr_ioq_uv *data = xdr_ioq_uv_create(0, UIO_FLAG_BUFQ);

		data->v.vio_base =
		data->v.vio_head =
		data->v.vio_tail = b;
		data->v.vio_wrap = (char *)b + xd->sm_dr.sendsz;
		data->u.uio_p1 = &xd->outbufs.uvqh;
		data->u.uio_p2 = xd->mr;
		TAILQ_INSERT_TAIL(&xd->outbufs.uvqh.qh, &data->uvq, q);

		b += xd->sm_dr.sendsz;
	}
	__warnx(TIRPC_DEBUG_FLAG_ERROR,
	"%s() NFS/FABRIC buffer_aligned at %p, buffer_total %d,  rx depth %d, rx sendsz %d. xd->xa->rq_depth %d, xd->xa->sq_depth %d, xd->xa->credits %d.",
		__func__, xd->buffer_aligned, xd->buffer_total,  xd->xa->sq_depth, xd->sm_dr.sendsz,
		xd->xa->rq_depth,
		xd->xa->sq_depth,
		xd->xa->credits);

	rc = rpc_fabric_setup_cbq(&xd->cbqh,
				xd->xa->rq_depth +
				xd->xa->sq_depth,
				xd->xa->credits);
	if (rc) {
		__warnx(TIRPC_DEBUG_FLAG_ERROR,
			"NFS/FABRIC %s:%u ERROR (return)",
			__func__, __LINE__);
		return 0;
	}

	//while (xd->sm_dr.ioq.ioq_uv.uvqh.qcount < CALLQ_SIZE) {
	//	xdr_rdma_callq(xd);
	//}
	return 0;
}




/*
 * svc_rdma_rendezvous: waits for connection request
 */
enum xprt_stat
svc_fabric_rendezvous(SVCXPRT *xprt)
{
	//SVCXPRT *xprt = 
	//struct sockaddr_storage *ss;
	//RDMAXPRT *req_xd = RDMA_DR(REC_XPRT(xprt));
	//RDMAXPRT *xd = rpc_rdma_accept_wait(req_xd,
	//			    __svc_params->idle_timeout);

	RDMAXPRT *xd = (RDMAXPRT *)xprt;

	if (!xd) {
		__warnx(TIRPC_DEBUG_FLAG_ERROR,
			"NFS/FABRIC %s:%u ERROR (return)",
			__func__, __LINE__);
		return (XPRT_DIED);
	}

	xd->sm_dr.xprt.xp_flags = SVC_XPRT_FLAG_CLOSE
				| SVC_XPRT_FLAG_INITIAL
				| SVC_XPRT_FLAG_INITIALIZED;
	/* fixme: put something here, but make it not work on fd operations. */
	xd->sm_dr.xprt.xp_fd = -1;
#if 0
	ss = (struct sockaddr_storage *)rdma_get_local_addr(xd->cm_id);
	__rpc_address_setup(&xd->sm_dr.xprt.xp_local);
	memcpy(&xd->sm_dr.xprt.xp_local.nb.buf, ss,
		xd->sm_dr.xprt.xp_local.nb.len);

	ss = (struct sockaddr_storage *)rdma_get_peer_addr(xd->cm_id);
	__rpc_address_setup(&xd->sm_dr.xprt.xp_remote);
	memcpy(&xd->sm_dr.xprt.xp_remote.nb.buf, ss,
		xd->sm_dr.xprt.xp_remote.nb.len);
#endif


#if 0
	if (xdr_rdma_create(xd)) {
		SVC_DESTROY(&xd->sm_dr.xprt);
		return (XPRT_DESTROYED);
	}

	if (rpc_rdma_accept_finalize(xd)) {
		SVC_DESTROY(&xd->sm_dr.xprt);
		return (XPRT_DESTROYED);
	}

	SVC_REF(xprt, SVC_REF_FLAG_NONE);
#endif
	if (xdr_fabric_create(xd)) {
		SVC_DESTROY(&xd->sm_dr.xprt);
		return (XPRT_DESTROYED);
	}
#if 0
	xd->sm_dr.xprt.xp_parent = xprt;
	if (xprt->xp_dispatch.rendezvous_cb(&xd->sm_dr.xprt)
	 || svc_rqst_xprt_register(&xd->sm_dr.xprt, xprt)) {
		SVC_DESTROY(&xd->sm_dr.xprt);
		return (XPRT_DESTROYED);
	}
#endif
	return (XPRT_IDLE);
}


#if 1

#define DUMP_BYTES_PER_GROUP (4)
#define DUMP_GROUPS_PER_LINE (4)
#define DUMP_BYTES_PER_LINE (DUMP_BYTES_PER_GROUP * DUMP_GROUPS_PER_LINE)

static void
rpcrdma_dump_msg(struct xdr_ioq_uv *data, char *comment, uint32_t xid)
{
	char *buffer;
	uint8_t *datum = data->v.vio_head;
	int sized = ioquv_length(data);
	int buffered = (((sized / DUMP_BYTES_PER_LINE) + 1 /*partial line*/)
			* (12 /* heading */
			   + (((DUMP_BYTES_PER_GROUP * 2 /*%02X*/) + 1 /*' '*/)
			      * DUMP_GROUPS_PER_LINE)))
			      * 			+ 1 /*'\0'*/;
	int i = 0;
	int m = 0;

	xid = ntohl(xid);
	if (sized == 0) {
		__warnx(TIRPC_DEBUG_FLAG_XDR,
			"rpcrdma 0x%" PRIx32 "(%" PRIu32 ") %s?",
			xid, xid, comment);
		return;
	}
	buffer = (char *)mem_alloc(buffered);

	while (sized > i) {
		int j = sized - i;
		int k = j < DUMP_BYTES_PER_LINE ? j : DUMP_BYTES_PER_LINE;
		int l = 0;
		int r = sprintf(&buffer[m], "\n%10d:", i);	/* heading */

		if (r < 0)
			goto quit;
		m += r;

		for (; l < k; l++) {
			if (l % DUMP_BYTES_PER_GROUP == 0)
				buffer[m++] = ' ';

			r = sprintf(&buffer[m], "%02X", datum[i++]);
			if (r < 0)
				goto quit;
			m += r;
		}
	}
quit:
	buffer[m] = '\0';	/* in case of error */
	__warnx(TIRPC_DEBUG_FLAG_ERROR,
		"NFS/FABRIC rpcrdma 0x%" PRIx32 "(%" PRIu32 ") %s:%s\n",
		xid, xid, comment, buffer);
	mem_free(buffer, buffered);
}
#endif /* rpcrdma_dump_msg */

/*
 * ** match RFC-5666bis as closely as possible
 * */
struct xdr_rdma_segment {
	uint32_t handle;	/* Registered memory handle */
	uint32_t length;	/* Length of the chunk in bytes */
	uint64_t offset;	/* Chunk virtual address or offset */
};

struct xdr_read_list {
	uint32_t present;	/* 1 indicates presence */
	uint32_t position;	/* Position in XDR stream */
	struct xdr_rdma_segment target;
};

struct xdr_write_chunk {
	struct xdr_rdma_segment target;
};

struct xdr_write_list {
	uint32_t present;	/* 1 indicates presence */
	uint32_t elements;	/* Number of array elements */
	struct xdr_write_chunk entry[0];
};


struct rpc_rdma_header {
	uint32_t rdma_reads;
	uint32_t rdma_writes;
	uint32_t rdma_reply;
	/* rpc body follows */
};

struct rpc_rdma_header_nomsg {
	uint32_t rdma_reads;
	uint32_t rdma_writes;
	uint32_t rdma_reply;
};


struct rdma_msg {
	uint32_t rdma_xid;	/* Mirrors the RPC header xid */
	uint32_t rdma_vers;	/* Version of this protocol */
	uint32_t rdma_credit;	/* Buffers requested/granted */
	uint32_t rdma_type;	/* Type of message (enum rdma_proc) */
	union {
		struct rpc_rdma_header		rdma_msg;
		struct rpc_rdma_header_nomsg	rdma_nomsg;
	} rdma_body;
};


#define m_(ptr) ((struct rdma_msg *)ptr)
#define xrl(ptr) ((struct xdr_read_list*)ptr)

typedef struct xdr_write_list wl_t;
#define xwl(ptr) ((struct xdr_write_list*)ptr)

static inline void
xdr_rdma_skip_read_list(uint32_t **pptr)
{
	while (xrl(*pptr)->present) {
		*pptr += sizeof(struct xdr_read_list)
			 / sizeof(**pptr);
	}
	(*pptr)++;
}

static inline void
xdr_rdma_skip_write_list(uint32_t **pptr)
{
	if (xwl(*pptr)->present) {
		*pptr += (sizeof(struct xdr_write_list)
			  + sizeof(struct xdr_write_chunk)
			    * ntohl(xwl(*pptr)->elements))
			 / sizeof(**pptr);
	}
	(*pptr)++;
}

static inline void
xdr_rdma_skip_reply_array(uint32_t **pptr)
{
	if (xwl(*pptr)->present) {
		*pptr += (sizeof(struct xdr_write_list)
			  + sizeof(struct xdr_write_chunk)
			    * ntohl(xwl(*pptr)->elements))
			 / sizeof(**pptr);
	} else {
		(*pptr)++;
	}
}

static inline uint32_t *
xdr_rdma_get_read_list(void *data)
{
	return &m_(data)->rdma_body.rdma_msg.rdma_reads;
}

static inline uint64_t decode_hyper(uint64_t *iptr)
{
	return ((uint64_t) ntohl(((uint32_t*)iptr)[0]) << 32)
		| (ntohl(((uint32_t*)iptr)[1]));
}
static inline uint32_t *
xdr_rdma_get_write_array(void *data)
{
	uint32_t *ptr = xdr_rdma_get_read_list(data);

	xdr_rdma_skip_read_list(&ptr);

	return ptr;
}

static inline uint32_t *
xdr_rdma_get_reply_array(void *data)
{
	uint32_t *ptr = xdr_rdma_get_read_list(data);

	xdr_rdma_skip_read_list(&ptr);
	xdr_rdma_skip_write_list(&ptr);

	return ptr;
}

static inline uint32_t *
xdr_rdma_skip_header(struct rdma_msg *rmsg)
{
	uint32_t *ptr = &rmsg->rdma_body.rdma_msg.rdma_reads;

	xdr_rdma_skip_read_list(&ptr);
	xdr_rdma_skip_write_list(&ptr);
	xdr_rdma_skip_reply_array(&ptr);

	return ptr;
}

static inline uintptr_t
xdr_rdma_header_length(struct rdma_msg *rmsg)
{
	uint32_t *ptr = xdr_rdma_skip_header(rmsg);

	return ((uintptr_t)ptr - (uintptr_t)rmsg);
}

bool
xdr_fabric_svc_recv(struct rpc_rdma_cbc *cbc, u_int32_t xid)
{
	cbc->call_uv = IOQ_(TAILQ_FIRST(&cbc->workq.ioq_uv.uvqh.qh));
	(cbc->call_uv->u.uio_references)++;
	cbc->call_head = cbc->call_uv->v.vio_head;

	__warnx(TIRPC_DEBUG_FLAG_ERROR,
			"NFS/FABRIC %s: decode  xdr_svc_recv cbc %p, head %p.", __func__, cbc, cbc->call_head);

	__warnx(TIRPC_DEBUG_FLAG_ERROR,
			"NFS/FABRIC %s: decode  context %s.", __func__, cbc->call_head);


	struct rdma_msg *cmsg;
	cbc->call_uv = IOQ_(TAILQ_FIRST(&cbc->workq.ioq_uv.uvqh.qh));
	(cbc->call_uv->u.uio_references)++;
	cbc->call_head = cbc->call_uv->v.vio_head;
	cmsg = (struct rdma_msg *)(cbc->call_head);
	rpcrdma_dump_msg(cbc->call_uv, "call", cmsg->rdma_xid);

	switch (ntohl(cmsg->rdma_vers)) {
	case 1:
		__warnx(TIRPC_DEBUG_FLAG_ERROR,
				"NFS/FABRIC %s: rdma_vers %.d.", __func__, ntohl(cmsg->rdma_vers));
		break;
	default:
		__warnx(TIRPC_DEBUG_FLAG_ERROR,
				"NFS/FABRIC %s: rdma_vers faild %" PRIu32 "?", __func__, ntohl(cmsg->rdma_vers));
		return (false);
	}
	/* locate NFS/RDMA (RFC-5666) chunk positions */
	cbc->read_chunk = xdr_rdma_get_read_list(cmsg);
	cbc->write_chunk = (wl_t *)cbc->read_chunk;
	xdr_rdma_skip_read_list((uint32_t **)&cbc->write_chunk);
	cbc->reply_chunk = cbc->write_chunk;
	xdr_rdma_skip_write_list((uint32_t **)&cbc->reply_chunk);
	cbc->call_data = cbc->reply_chunk;
	xdr_rdma_skip_reply_array((uint32_t **)&cbc->call_data);

	xdr_ioq_release(&cbc->holdq.ioq_uv.uvqh);
	
	/* swap calling message from workq to holdq */
	TAILQ_CONCAT(&cbc->holdq.ioq_uv.uvqh.qh, &cbc->workq.ioq_uv.uvqh.qh, q);
	cbc->holdq.ioq_uv.uvqh.qcount = cbc->workq.ioq_uv.uvqh.qcount;
	cbc->workq.ioq_uv.uvqh.qcount = 0;

	/* skip past the header for the calling buffer */
	xdr_ioq_reset(&cbc->holdq, ((uintptr_t)cbc->call_data
				  - (uintptr_t)cmsg));


//	uint32_t k;
//	uint32_t l;

	while (((struct xdr_read_list*)(cbc->read_chunk))->present != 0){
//	    && xrl(cbc->read_chunk)->position == 0) {

//		l = ntohl(xrl(cbc->read_chunk)->target.length);
//
		uint32_t handle = ntohl(xrl(cbc->read_chunk)->target.handle);
		uint32_t length = ntohl(xrl(cbc->read_chunk)->target.length);
		uint64_t offset = decode_hyper(&(xrl(cbc->read_chunk)->target.offset));

		__warnx(TIRPC_DEBUG_FLAG_ERROR,
			"NFS/FABRIC %s: chunk handle %d, length %d, offset %ld.", __func__, handle, length, offset);

#if 0
		k = xdr_rdma_chunk_fetch(&cbc->workq, &xprt->inbufs.uvqh,
					 "call chunk", l,
					 xprt->sm_dr.recvsz,
					 xprt->xa->max_recv_sge,
					 xdr_rdma_chunk_in);

		xdr_rdma_wait_read_cb(xprt, cbc, k, &rl(cbc->read_chunk)->target);
		rpcrdma_dump_msg(IOQ_(TAILQ_FIRST(&cbc->workq.ioq_uv.uvqh.qh)),
				 "call chunk", cmsg->rdma_xid);
#endif
		/* concatenate any additional buffers after the calling message,
 * 		 * faking there is more call data in the calling buffer.
 * 		 		 */
		TAILQ_CONCAT(&cbc->holdq.ioq_uv.uvqh.qh,
			     &cbc->workq.ioq_uv.uvqh.qh, q);
		cbc->holdq.ioq_uv.uvqh.qcount += cbc->workq.ioq_uv.uvqh.qcount;
		cbc->workq.ioq_uv.uvqh.qcount = 0;
		cbc->read_chunk = (char *)cbc->read_chunk
						+ sizeof(struct xdr_read_list);

	}
	//post_recv(global_xd);

#if 0
	RDMAXPRT *xprt;
	struct rdma_msg *cmsg;
	uint32_t k;
	uint32_t l;

	if (!cbc) {
		__warnx(TIRPC_DEBUG_FLAG_ERROR,
			"%s() no context?",
			__func__);
		return (false);
	}
	xprt = x_xprt(cbc->workq.xdrs);

	/* free old buffers (should do nothing) */
	xdr_ioq_release(&cbc->holdq.ioq_uv.uvqh);
	xdr_rdma_callq(xprt);

	cbc->call_uv = IOQ_(TAILQ_FIRST(&cbc->workq.ioq_uv.uvqh.qh));
	(cbc->call_uv->u.uio_references)++;
	cbc->call_head = cbc->call_uv->v.vio_head;
	cmsg = m_(cbc->call_head);
	rpcrdma_dump_msg(cbc->call_uv, "call", cmsg->rdma_xid);

	switch (ntohl(cmsg->rdma_vers)) {
	case RPCRDMA_VERSION:
		break;
	default:
		__warnx(TIRPC_DEBUG_FLAG_ERROR,
			"%s() rdma_vers %" PRIu32 "?",
			__func__, ntohl(cmsg->rdma_vers));
		xdr_rdma_encode_error(cbc->call_uv, RDMA_ERR_VERS);
		xdr_rdma_post_send_cb(xprt, cbc, 1);
		xdr_ioq_uv_release(cbc->call_uv);
		return (false);
	}

	switch (ntohl(cmsg->rdma_type)) {
	case RDMA_MSG:
	case RDMA_NOMSG:
		break;
	default:
		__warnx(TIRPC_DEBUG_FLAG_ERROR,
			"%s() rdma_type %" PRIu32 "?",
			__func__, ntohl(cmsg->rdma_type));
		xdr_rdma_encode_error(cbc->call_uv, RDMA_ERR_BADHEADER);
		xdr_rdma_post_send_cb(xprt, cbc, 1);
		xdr_ioq_uv_release(cbc->call_uv);
		return (false);
	}

	/* locate NFS/RDMA (RFC-5666) chunk positions */
	cbc->read_chunk = xdr_rdma_get_read_list(cmsg);
	cbc->write_chunk = (wl_t *)cbc->read_chunk;
	xdr_rdma_skip_read_list((uint32_t **)&cbc->write_chunk);
	cbc->reply_chunk = cbc->write_chunk;
	xdr_rdma_skip_write_list((uint32_t **)&cbc->reply_chunk);
	cbc->call_data = cbc->reply_chunk;
	xdr_rdma_skip_reply_array((uint32_t **)&cbc->call_data);

	/* swap calling message from workq to holdq */
	TAILQ_CONCAT(&cbc->holdq.ioq_uv.uvqh.qh, &cbc->workq.ioq_uv.uvqh.qh, q);
	cbc->holdq.ioq_uv.uvqh.qcount = cbc->workq.ioq_uv.uvqh.qcount;
	cbc->workq.ioq_uv.uvqh.qcount = 0;

	/* skip past the header for the calling buffer */
	xdr_ioq_reset(&cbc->holdq, ((uintptr_t)cbc->call_data
				  - (uintptr_t)cmsg));

	while (rl(cbc->read_chunk)->present != 0
	    && rl(cbc->read_chunk)->position == 0) {
		l = ntohl(rl(cbc->read_chunk)->target.length);
		k = xdr_rdma_chunk_fetch(&cbc->workq, &xprt->inbufs.uvqh,
					 "call chunk", l,
					 xprt->sm_dr.recvsz,
					 xprt->xa->max_recv_sge,
					 xdr_rdma_chunk_in);

		xdr_rdma_wait_read_cb(xprt, cbc, k, &rl(cbc->read_chunk)->target);
		rpcrdma_dump_msg(IOQ_(TAILQ_FIRST(&cbc->workq.ioq_uv.uvqh.qh)),
				 "call chunk", cmsg->rdma_xid);

		/* concatenate any additional buffers after the calling message,
		 * faking there is more call data in the calling buffer.
		 */
		TAILQ_CONCAT(&cbc->holdq.ioq_uv.uvqh.qh,
			     &cbc->workq.ioq_uv.uvqh.qh, q);
		cbc->holdq.ioq_uv.uvqh.qcount += cbc->workq.ioq_uv.uvqh.qcount;
		cbc->workq.ioq_uv.uvqh.qcount = 0;
		cbc->read_chunk = (char *)cbc->read_chunk
						+ sizeof(struct xdr_read_list);
	}
#endif
	return (true);
}



static enum xprt_stat
svc_fabric_decode(struct svc_req *req)
{
	XDR *xdrs = req->rq_xdrs;
	//struct xdr_ioq *holdq = XIOQ(xdrs);


	/*这里是收包和解析的过程*/

	__warnx(TIRPC_DEBUG_FLAG_ERROR,
		"%s() NFS/FABRIC start decode() req %p, xdrs %p.", __func__, req, xdrs);

	if (!xdr_fabric_svc_recv(global_cbc, 0)){
		__warnx(TIRPC_DEBUG_FLAG_ERROR,
			"NFS/FABRIC %s: xdr_rdma_svc_recv failed",
			__func__);
		return (XPRT_DIED);
	}

	xdrs->x_op = XDR_DECODE;
	/* No need, already positioned to beginning ...
	XDR_SETPOS(xdrs, 0);
	 */
	rpc_msg_init(&req->rq_msg);

	if (!xdr_dplx_decode(xdrs, &req->rq_msg)) {
		__warnx(TIRPC_DEBUG_FLAG_ERROR,
			"NFS/FABRIC %s: xdr_dplx_decode failed",
			__func__);
		return (XPRT_DIED);
	}

	/* the checksum */
	req->rq_cksum = 0;
	req->rq_xprt->xp_parent = req->rq_xprt;
	req->rq_xprt->xp_ops = &rpc_fabric_ops;
	/*nfs_rpc_dispatch_RDMA 这个已经在create_rdma的时候注册过了*/
	//(void)req->rq_xprt->xp_dispatch.rendezvous_cb(req->rq_xprt);
	__warnx(TIRPC_DEBUG_FLAG_ERROR,
			"NFS/FABRIC %s: calll dispatch processcb , req %p",
			__func__,req);
	return req->rq_xprt->xp_dispatch.process_cb(req);
}

static int
xdr_fabric_wrap_callback(struct rpc_rdma_cbc *cbc, RDMAXPRT *xprt)
{
	XDR *xdrs = cbc->holdq.xdrs;
	/*
	call svc_fabric_decode
	*/
	__warnx(TIRPC_DEBUG_FLAG_ERROR,
		"%s() NFS/FABRIC wrap call back call to svc_request() cbc %p, xprt %p.", __func__, cbc, xprt);
	return (int)svc_request(&xprt->sm_dr.xprt, xdrs);
}


/**
 * rpc_rdma_cm_thread: thread function which waits for new connection events
 * and gives them to handler (then ack the event)
 *
 */
static void *
rpc_fabric_thread(void *nullarg)
{
	RDMAXPRT *xd = (RDMAXPRT *)nullarg;
	int rc;
	/*初始化各种rdma服务*/
	hints = fi_allocinfo();
	if (!hints)
		return NULL;
	#if 1
	hints->ep_attr->type = FI_EP_MSG; // 可靠数据报端点, 类似socket, 但无须执行listen/connect/accept
	hints->caps = FI_MSG;
 	hints->fabric_attr->prov_name = "verbs";
	hints->addr_format = 0;
	hints->tx_attr->op_flags = FI_DELIVERY_COMPLETE;
	hints->tx_attr->tclass = 513;
	hints->domain_attr->threading = FI_THREAD_DOMAIN;
	hints->domain_attr->mr_mode = FI_MR_LOCAL | FI_MR_ENDPOINT | OFI_MR_BASIC_MAP | FI_MR_RAW;
	hints->tx_attr->op_flags = 0;
	#else

	hints->ep_attr->type = FI_EP_MSG; // 可靠数据报端点, 类似socket, 但无须执行listen/connect/accept
	hints->caps = FI_MSG | FI_RMA;
 	hints->fabric_attr->prov_name = "verbs";
	hints->addr_format = 0;
	hints->tx_attr->op_flags = FI_DELIVERY_COMPLETE;
	hints->tx_attr->tclass = 513 | FI_TC_BULK_DATA; 
	hints->domain_attr->threading = FI_THREAD_DOMAIN;
	hints->domain_attr->mr_mode = FI_MR_LOCAL | FI_MR_ENDPOINT | OFI_MR_BASIC_MAP | FI_MR_RAW ;
	hints->domain_attr->resource_mgmt = FI_RM_ENABLED;
	hints->tx_attr->op_flags = 0;
	hints->mode = FI_CONTEXT;
	#endif

	rc = start_server(xd);
	__warnx(TIRPC_DEBUG_FLAG_ERROR,
			"%s() NFS/FABRIC start server, rc=%d.", __func__, rc);
	if (rc) {
		return NULL;
	}

	/*复用同一个xprt, 里面申请内存*/
	if (XPRT_DESTROYED == svc_fabric_rendezvous(&(xd->sm_dr.xprt)) )
	{
		__warnx(TIRPC_DEBUG_FLAG_ERROR,
			"%s() NFS/FABRIC  rendezvous failed, rc=%d.", __func__,rc);
		return NULL;
	}

	rc = server_connect(xd);
	if (rc) {
		__warnx(TIRPC_DEBUG_FLAG_ERROR,
				"%s() NFS/FABRIC start server fiald, rc=%d.", __func__, rc);
		return NULL;
	}
	struct sockaddr_storage ss;
	size_t tmplen = sizeof(struct sockaddr_storage);
	
	fi_getname(&ep->fid, &ss, &tmplen);

	__rpc_address_setup(&xd->sm_dr.xprt.xp_local);
	memcpy(&xd->sm_dr.xprt.xp_local.nb.buf, &ss,
		xd->sm_dr.xprt.xp_local.nb.len);

	__rpc_address_setup(&xd->sm_dr.xprt.xp_remote);
	memcpy(&xd->sm_dr.xprt.xp_remote.nb.buf, &ss,
		xd->sm_dr.xprt.xp_remote.nb.len);	

	rc = post_recv(xd);
	if (!rc) {
		rc = wait_recvcq();
		__warnx(TIRPC_DEBUG_FLAG_ERROR,
				"%s() NFS/FABRIC recv msg rc %d.", __func__, rc);
		//		"%s() NFS/FABRIC recv msg: \"%s\", rc %d.", __func__, xd->buffer_aligned, rc);
		xdr_fabric_wrap_callback(global_cbc, xd);
	} else {
		__warnx(TIRPC_DEBUG_FLAG_ERROR,
				"%s() NFS/FABRIC  post recv faild, rc=%d.", __func__, rc);
	}
	while (1){
			rc = post_recv(xd);
			if (!rc) {
				rc = wait_recvcq();
				__warnx(TIRPC_DEBUG_FLAG_ERROR,
				//		"%s() NFS/FABRIC recv msg: \"%s\", rc %d.", __func__, xd->buffer_aligned, rc);
						"%s() NFS/FABRIC recv msg rc %d.", __func__, rc);
				xdr_fabric_wrap_callback(global_cbc, xd);
			} else {
				__warnx(TIRPC_DEBUG_FLAG_ERROR,
						"%s() NFS/FABRIC  post recv faild, rc=%d.", __func__, rc);
				break;
			}
	}

	return NULL;

}


/**
 * rpc_rdma_thread_create: Simple wrapper around pthread_create
 */
static int
rpc_fabric_thread_create(pthread_t *thrid, size_t stacksize,
		       void *(*routine)(void *), void *arg)
{

	pthread_attr_t attr;
	int rc;

	/* Init for thread parameter (mostly for scheduling) */
	rc = pthread_attr_init(&attr);
	if (rc) {
		__warnx(TIRPC_DEBUG_FLAG_ERROR,
			"%s() can't init pthread's attributes: %s (%d)",
			__func__, strerror(rc), rc);
		return rc;
	}

	rc = pthread_attr_setscope(&attr, PTHREAD_SCOPE_SYSTEM);
	if (rc) {
		__warnx(TIRPC_DEBUG_FLAG_ERROR,
			"%s() can't set pthread's scope: %s (%d)",
			__func__, strerror(rc), rc);
		return rc;
	}

	rc = pthread_attr_setdetachstate(&attr, PTHREAD_CREATE_JOINABLE);
	if (rc) {
		__warnx(TIRPC_DEBUG_FLAG_ERROR,
			"%s() can't set pthread's join state: %s (%d)",
			__func__, strerror(rc), rc);
		return rc;
	}

	rc = pthread_attr_setstacksize(&attr, stacksize);
	if (rc) {
		__warnx(TIRPC_DEBUG_FLAG_ERROR,
			"%s() can't set pthread's stack size: %s (%d)",
			__func__, strerror(rc), rc);
		return rc;
	}

	return pthread_create(thrid, &attr, routine, arg);
}


/**
 * rpc_rdma_allocate: allocate rdma transport structures
 *
 * @param[IN] xa	parameters
 *
 * @return xprt on success, NULL on failure
 */
static RDMAXPRT *
rpc_fabric_allocate(const struct rpc_rdma_attr *xa)
{
	RDMAXPRT *xd;
	int rc;

	if (!xa) {
		__warnx(TIRPC_DEBUG_FLAG_ERROR,
			"%s() Invalid argument",
			__func__);
		return NULL;
	}

	xd = mem_zalloc(sizeof(*xd));

	xd->sm_dr.xprt.xp_type = XPRT_RDMA;
	xd->sm_dr.xprt.xp_refcnt = 1;
	xd->sm_dr.xprt.xp_ops = &rpc_fabric_ops;

	xd->xa = xa;
	xd->conn_type = RDMA_PS_TCP;
	xd->destroy_on_disconnect = xa->destroy_on_disconnect;

	/* initialize locking first, will be destroyed last (above).
	 */
	xdr_ioq_setup(&xd->sm_dr.ioq);
	rpc_dplx_rec_init(&xd->sm_dr);

	rc = mutex_init(&xd->cm_lock, NULL);
	if (rc) {
		__warnx(TIRPC_DEBUG_FLAG_ERROR,
			"%s() mutex_init failed: %s (%d)",
			__func__, strerror(rc), rc);
		goto cm_lock;
	}

	rc = cond_init(&xd->cm_cond, NULL, NULL);
	if (rc) {
		__warnx(TIRPC_DEBUG_FLAG_ERROR,
			"%s() cond_init failed: %s (%d)",
			__func__, strerror(rc), rc);
		goto cm_cond;
	}

	return (xd);

cm_cond:
	mutex_destroy(&xd->cm_lock);
cm_lock:
	mutex_destroy(&xd->sm_dr.xprt.xp_lock);

	mem_free(xd, sizeof(*xd));
	return NULL;
}


/**
 * rpc_rdma_ncreatef: initialize rdma transport structures
 *
 * @param[IN] xa		parameters
 * @param[IN] sendsize;		max send size
 * @param[IN] recvsize;		max recv size
 * @param[IN] flags; 		unused
 *
 * @return xprt on success, NULL on failure
 */
SVCXPRT *
rpc_fabric_ncreatef(const struct rpc_rdma_attr *xa,
		  const u_int sendsize, const u_int recvsize,
		  const uint32_t flags)
{
	RDMAXPRT *xd;
	int rc;

	if (xa->backlog > 4096) {
		__warnx(TIRPC_DEBUG_FLAG_ERROR,
			"%s() backlog (%u) much too large",
			__func__, xa->backlog);
		return NULL;
	}

	xd = rpc_fabric_allocate(xa);
	if (!xd) {
		__warnx(TIRPC_DEBUG_FLAG_ERROR,
			"%s:%u ERROR (return)",
			__func__, __LINE__);
		return NULL;
	}
	xd->server = xa->backlog; /* convenient number > 0 */


	pthread_mutex_lock(&svc_work_pool.pqh.qmutex);
	if (!svc_work_pool.params.thrd_max) {
		pthread_mutex_unlock(&svc_work_pool.pqh.qmutex);

		__warnx(TIRPC_DEBUG_FLAG_ERROR,
			"%s() svc_work_pool already shutdown",
			__func__);
		goto failure;
	}
	pthread_mutex_unlock(&svc_work_pool.pqh.qmutex);

	/* buffer sizes MUST be page sized */
	xd->sm_dr.pagesz = sysconf(_SC_PAGESIZE);
	if (recvsize) {
		/* round up */
		xd->sm_dr.recvsz = recvsize + (xd->sm_dr.pagesz - 1);
		xd->sm_dr.recvsz &= ~(xd->sm_dr.pagesz - 1);
	} else {
		/* default */
		xd->sm_dr.recvsz = xd->sm_dr.pagesz;
	}
	if (sendsize) {
		/* round up */
		xd->sm_dr.sendsz = sendsize + (xd->sm_dr.pagesz - 1);
		xd->sm_dr.sendsz &= ~(xd->sm_dr.pagesz - 1);
	} else {
		/* default */
		xd->sm_dr.recvsz = xd->sm_dr.pagesz;
	}
#if 0
	/* round up to the next power of two */
	rpc_rdma_state.c_r.q_size = 2;
	while (rpc_rdma_state.c_r.q_size < xa->backlog) {
		rpc_rdma_state.c_r.q_size <<= 1;
	}
	rpc_rdma_state.c_r.id_queue = mem_alloc(rpc_rdma_state.c_r.q_size
						* sizeof(struct rdma_cm_id *));
	sem_init(&rpc_rdma_state.c_r.u_sem, 0, rpc_rdma_state.c_r.q_size);
#endif

	__warnx(TIRPC_DEBUG_FLAG_RPC_RDMA,
		"%s() NFS/RDMA engine bound",
		__func__);
	pthread_t thrid;
	rc = rpc_fabric_thread_create(&thrid, 65536,
				rpc_fabric_thread, (void *)xd);
	__warnx(TIRPC_DEBUG_FLAG_ERROR,
			"%s() NFS/FABRIC create thread, rc=%d.", __func__,rc);

	return (&xd->sm_dr.xprt);

failure:
	//rpc_rdma_destroy(xd);
	return NULL;
}


static void
rpc_fabric_unlink_it(SVCXPRT *xprt, u_int flags, const char *tag, const int line)
{
	return;
}
static void
rpc_fabric_destroy_it(SVCXPRT *xprt, u_int flags, const char *tag, const int line)
{
	return;
}

static bool
/*ARGSUSED*/
rpc_fabric_control(SVCXPRT *xprt, const u_int rq, void *in)
{
	return (TRUE);
}

enum xprt_stat
svc_fabric_stat(SVCXPRT *xprt)
{
	if (!xprt)
		return (XPRT_IDLE);

	if (xprt->xp_flags & SVC_XPRT_FLAG_DESTROYED)
		return (XPRT_DESTROYED);

	return (XPRT_IDLE);
}
static enum xprt_stat  svc_fabric_reply(struct svc_req *req);

extern mutex_t ops_lock;
struct xp_ops rpc_fabric_ops = {
	.xp_recv = svc_fabric_rendezvous,
	.xp_stat = svc_fabric_stat,
	.xp_reply = svc_fabric_reply,
	.xp_decode = svc_fabric_decode,
	.xp_checksum = NULL,		/* not used */
	.xp_unlink = rpc_fabric_unlink_it,
	.xp_destroy = rpc_fabric_destroy_it,
	.xp_control = rpc_fabric_control,
	.xp_free_user_data = NULL,	/* no default */
};
static int
xdr_fabric_write_cb(RDMAXPRT *xprt, struct rpc_rdma_cbc *cbc, int sge,
		      struct xdr_rdma_segment *rs)
{
	int ret  = 0; 
	int i = 0;
	uint32_t totalsize = 0;	
	struct poolq_entry *have = TAILQ_FIRST(&cbc->workq.ioq_uv.uvqh.qh);

	struct iovec send_iov[4];

	
	if (have == NULL)
		return 0;

	while (have && i < sge) {
		//struct ibv_mr *mr = IOQ_(have)->u.uio_p2;
		uint32_t length = ioquv_length(IOQ_(have));
		cbc->sg_list[i].addr = (uintptr_t)(IOQ_(have)->v.vio_head);
		cbc->sg_list[i].length = length;
		//cbc->sg_list[i++].lkey = mr->lkey;
		//
		send_iov[i].iov_base = (void *)(IOQ_(have)->v.vio_head);	
		send_iov[i].iov_len = length;
		
		totalsize += length;
		have = TAILQ_NEXT(have, q);
		__warnx(TIRPC_DEBUG_FLAG_ERROR,
				"%s() NFS/FABRIC sg[%d] addr %p length %d.", __func__, 
				i, cbc->sg_list[i].addr, cbc->sg_list[i].length);	
		i ++;

	}
		__warnx(TIRPC_DEBUG_FLAG_ERROR,
				"%s() NFS/FABRIC totalsize %d. sge %d.", __func__, 
			totalsize, sge);	
	//if (totalsize == 0)
	//	return 0;

	if (rs != NULL) {

		uint64_t	remote_addr = decode_hyper(&rs->offset);
		uint32_t	rkey =  ntohl(rs->handle);
		uint32_t    length = ntohl(rs->length);
	#if 0
		uint64_t	remote_cq_data = 0;
		struct fi_context *ctx = NULL;

		struct fi_msg_rma rma_msg;
		struct fi_rma_iov rma_iov;

		rma_iov.addr = remote_addr;
		rma_iov.len = length;
		rma_iov.key = rkey;
		
		rma_msg.msg_iov = send_iov;
		rma_msg.desc = NULL;
		rma_msg.iov_count = sge;
		rma_msg.addr = remote_fi_addr;
		rma_msg.rma_iov = &rma_iov;
		rma_msg.rma_iov_count = 1;
		rma_msg.context = ctx;
		rma_msg.data = remote_cq_data;
		ret = fi_writemsg(ep, &rma_msg, 0);
	#else
		char buf[1024];
		memset(buf, 0, 1024);
		int i = 0,offset = 0;
		//for (; i<sge-1; i++) {
		//	offset += send_iov[i].iov_len;	
		//	memcpy(send_iov[0].iov_base + offset , send_iov[i+1].iov_base,  send_iov[i+1].iov_len);
		//}
        for (; i<sge; i++) {
            memcpy(buf + offset , send_iov[i].iov_base,  send_iov[i].iov_len);
            offset += send_iov[i].iov_len;  
        }	
		//ret = fi_write(ep, &rma_msg, 0);
		//ret = fi_write(ep, send_iov[0].iov_base, totalsize, mr_desc, remote_fi_addr, remote_addr, rkey, NULL);
		ret = fi_write(ep, buf, totalsize, NULL, remote_fi_addr, remote_addr, (uint64_t)rkey, NULL);
	#endif	
		if (ret == 0){
			wait_sendcq();
			__warnx(TIRPC_DEBUG_FLAG_ERROR,
					"%s() NFS/FABRIC write success.", __func__);
		}else {
		            __warnx(TIRPC_DEBUG_FLAG_ERROR,
                    "%s() NFS/FABRIC write failed.", __func__);
		}

		__warnx(TIRPC_DEBUG_FLAG_ERROR,
					"%s() NFS/FABRIC rs remoteaddr %d rkey %d length %d.", __func__,
					remote_addr, rkey, length);

	}else {
	#if 0
		struct fi_context tx_ctx;
		struct fi_msg msg;

		msg.msg_iov = send_iov;
		msg.iov_count = sge;
		msg.addr = remote_fi_addr;
		msg.context = &tx_ctx;
		msg.data = 0;
		msg.desc = &mr_desc;

	#else
		char buf[1024];
		memset(buf, 0, 1024);
		int i = 0,offset = 0;
		#if 0
		for (; i<sge-1; i++) {
			offset += send_iov[i].iov_len;	
			memcpy(send_iov[0].iov_base + offset , send_iov[i+1].iov_base,  send_iov[i+1].iov_len);
		}
		#endif

        for (; i<sge; i++) {
            memcpy(buf + offset , send_iov[i].iov_base,  send_iov[i].iov_len);
            offset += send_iov[i].iov_len;  
        }	

		//ret = fi_send(ep, send_iov[0].iov_base, totalsize, NULL, remote_fi_addr, NULL);
		do { 
			//ret = fi_send(ep, send_iov[0].iov_base, totalsize>200 ? 200 : totalsize, NULL, remote_fi_addr, NULL); 
			ret = fi_send(ep, buf, totalsize, NULL, remote_fi_addr, NULL); 
			if (ret && ret != -FI_EAGAIN) {
				FA_PRINT("error fi_send %d\n", ret); 
				return ret;
			}
			if (ret == -FI_EAGAIN) {
				print_cq_error(txcq);
				ret  = fi_cq_read(txcq, NULL, 0);
				FA_PRINT("error fi_send size %d, FI_EAGAIN ret:%d\n", totalsize, ret);

				sleep(1);
			}
		} while (0);

	#endif
		if (ret == 0){
			wait_sendcq();
			__warnx(TIRPC_DEBUG_FLAG_ERROR,
					"%s() NFS/FABRIC send success. totalsize %d.", __func__, totalsize);
		}else {
		            __warnx(TIRPC_DEBUG_FLAG_ERROR,
                    "%s() NFS/FABRIC send failed.", __func__);
		}
		
	}
	
	return ret;
}


#define x_xprt(xdrs) ((RDMAXPRT *)((xdrs)->x_lib[1]))
bool
xdr_fabric_svc_flushout(struct rpc_rdma_cbc *cbc)
{
	RDMAXPRT *xprt;
	struct rpc_msg *msg;
	struct rdma_msg *cmsg;
	struct rdma_msg *rmsg;
	struct xdr_write_list *w_array;
	struct xdr_write_list *reply_array;
	struct xdr_ioq_uv *head_uv;
	struct xdr_ioq_uv *work_uv;

	if (!cbc) {
		__warnx(TIRPC_DEBUG_FLAG_ERROR,
			"%s() no context?",
			__func__);
		return (false);
	}
	xprt = x_xprt(cbc->workq.xdrs);

	/* swap reply body from holdq to workq */
	TAILQ_CONCAT(&cbc->workq.ioq_uv.uvqh.qh, &cbc->holdq.ioq_uv.uvqh.qh, q);
	cbc->workq.ioq_uv.uvqh.qcount = cbc->holdq.ioq_uv.uvqh.qcount;
	cbc->holdq.ioq_uv.uvqh.qcount = 0;

	work_uv = IOQ_(TAILQ_FIRST(&cbc->workq.ioq_uv.uvqh.qh));
	msg = (struct rpc_msg *)(work_uv->v.vio_head);
	/* work_uv->v.vio_tail has been set by xdr_tail_update() */

	switch(ntohl(msg->rm_direction)) {
	    case CALL:
		__warnx(TIRPC_DEBUG_FLAG_ERROR,
			"%s() nothing to send on CALL (%u)",
			__func__, ntohl(msg->rm_direction));
		return (true);
	    case REPLY:
		/* good to go */
		break;
	    default:
		__warnx(TIRPC_DEBUG_FLAG_ERROR,
			"%s() bad rm_direction (%u)",
			__func__, ntohl(msg->rm_direction));
		return (false);
	}
	cmsg = m_(cbc->call_head);

	if (cmsg->rdma_xid != msg->rm_xid) {
		__warnx(TIRPC_DEBUG_FLAG_XDR,
			"%s() xid (%u) not equal RPC (%u)",
			__func__, ntohl(cmsg->rdma_xid), ntohl(msg->rm_xid));
		return (false);
	}

	/* usurp the holdq for the head, move to workq later */
	head_uv = IOQ_(xdr_ioq_uv_fetch(&cbc->holdq, &xprt->outbufs.uvqh,
					"sreply head", 1, IOQ_FLAG_NONE));

	/* entry was already added directly to the queue */
	head_uv->v.vio_head = head_uv->v.vio_base;
	/* tail adjusted below */
	head_uv->v.vio_wrap = (char *)head_uv->v.vio_base + xprt->sm_dr.sendsz;

	/* build the header that goes with the data */
	rmsg = m_(head_uv->v.vio_head);
	rmsg->rdma_xid = cmsg->rdma_xid;
	rmsg->rdma_vers = cmsg->rdma_vers;
	rmsg->rdma_credit = htonl(xprt->xa->credits);

	/* no read, write chunks. */
	rmsg->rdma_body.rdma_msg.rdma_reads = 0; /* htonl(0); */
	rmsg->rdma_body.rdma_msg.rdma_writes = 0; /* htonl(0); */

	reply_array = (wl_t *)cbc->reply_chunk;
	if (reply_array->present == 0) {
		rmsg->rdma_type = htonl(0); //RDMA_MSG

		/* no reply chunk either */
		rmsg->rdma_body.rdma_msg.rdma_reply = 0; /* htonl(0); */

		head_uv->v.vio_tail = head_uv->v.vio_head
					+ xdr_rdma_header_length(rmsg);

		rpcrdma_dump_msg(head_uv, "sreply head", msg->rm_xid);
		rpcrdma_dump_msg(work_uv, "sreply body", msg->rm_xid);
	} else {
		uint32_t i = 0;
		uint32_t n = ntohl(reply_array->elements);

		rmsg->rdma_type = htonl(1);//RDMA_NOMSG

		/* reply chunk */
		w_array = (wl_t *)&rmsg->rdma_body.rdma_msg.rdma_reply;
		w_array->present = htonl(1);

		while (i < n) {
			struct xdr_rdma_segment *c_seg =
				&reply_array->entry[i].target;
			struct xdr_rdma_segment *w_seg =
				&w_array->entry[i++].target;
			uint32_t length = ntohl(c_seg->length);
			uint32_t k = length / xprt->sm_dr.sendsz;
			uint32_t m = length % xprt->sm_dr.sendsz;

			if (m) {
				/* need fractional buffer */
				k++;
			}

			/* ensure never asking for more buffers than allowed */
			if (k > xprt->xa->max_send_sge) {
				__warnx(TIRPC_DEBUG_FLAG_XDR,
					"%s() requested chunk %" PRIu32
					" is too long (%" PRIu32 ">%" PRIu32 ")",
					__func__, length, k,
					xprt->xa->max_send_sge);
				k = xprt->xa->max_send_sge;
			}
			*w_seg = *c_seg;

			/* sometimes, back-to-back buffers could be sent
			 * together.  releases of unused buffers and
			 * other events eventually scramble the buffers
			 * enough that there's no gain in efficiency.
			 */
			xdr_fabric_write_cb(xprt, cbc, k, w_seg);

			__warnx(TIRPC_DEBUG_FLAG_ERROR,
					"%s() NFS/FABRIC reply array sge:%d.", __func__, k);
			while (0 < k--) {
				struct poolq_entry *have =
					TAILQ_FIRST(&cbc->workq.ioq_uv.uvqh.qh);

				TAILQ_REMOVE(&cbc->workq.ioq_uv.uvqh.qh, have, q);
				(cbc->workq.ioq_uv.uvqh.qcount)--;

				rpcrdma_dump_msg(IOQ_(have), "sreply body",
						 msg->rm_xid);
				xdr_ioq_uv_release(IOQ_(have));
			}

		}
//		__warnx(TIRPC_DEBUG_FLAG_ERROR,
//					"%s() NFS/FABRIC reply array %d.%d,", __func__, n, i);
		w_array->elements = htonl(i);

		head_uv->v.vio_tail = head_uv->v.vio_head
					+ xdr_rdma_header_length(rmsg);
		rpcrdma_dump_msg(head_uv, "sreply head", msg->rm_xid);

	}

	/* actual send, callback will take care of cleanup */
	TAILQ_REMOVE(&cbc->holdq.ioq_uv.uvqh.qh, &head_uv->uvq, q);
	(cbc->holdq.ioq_uv.uvqh.qcount)--;
	(cbc->workq.ioq_uv.uvqh.qcount)++;
	TAILQ_INSERT_HEAD(&cbc->workq.ioq_uv.uvqh.qh, &head_uv->uvq, q);
	
	__warnx(TIRPC_DEBUG_FLAG_ERROR,
		"%s() NFS/FABRIC reply array workq qcount :%d, reply present %d.", __func__, cbc->workq.ioq_uv.uvqh.qcount, reply_array->present);
	xdr_fabric_write_cb(xprt, cbc, cbc->workq.ioq_uv.uvqh.qcount, NULL);

#if 0
		{
			char buf[1024];
			memset(buf, 0, 1024);
			uint32_t head_length = ioquv_length(head_uv);
			uint32_t work_length = ioquv_length(work_uv);
			memcpy(buf,head_uv->v.vio_head, head_length);
			memcpy(buf + head_length, work_uv->v.vio_head, work_length);
			//struct poolq_entry *have = TAILQ_FIRST(&cbc->workq.ioq_uv.uvqh.qh);
			//uint32_t length = ioquv_length(IOQ_(have));
			//void *addr = (void *)(uintptr_t)(IOQ_(have)->v.vio_head);
			__warnx(TIRPC_DEBUG_FLAG_ERROR,
					"%s() NFS/FABRIC addr %p, size %d.", __func__, buf, head_length + work_length);
			post_send(buf, (ssize_t)head_length + work_length);
			wait_sendcq();
			__warnx(TIRPC_DEBUG_FLAG_ERROR,
					"%s() NFS/FABRIC send success.", __func__);

		}
#endif 

	/* free the old inbuf we only kept for header */
	xdr_ioq_uv_release(cbc->call_uv);
	return (true);
}

enum xprt_stat
svc_fabric_reply(struct svc_req *req)
{
	XDR *xdrs = req->rq_xdrs;
	struct xdr_ioq *holdq = XIOQ(xdrs);
	struct rpc_rdma_cbc *cbc =
		opr_containerof(holdq, struct rpc_rdma_cbc, holdq);

	__warnx(TIRPC_DEBUG_FLAG_SVC_RDMA,
		"%s() xprt %p req %p cbc %p outgoing xdr %p\n",
		__func__, req->rq_xprt, req, cbc, xdrs);

	if (!xdr_rdma_svc_reply(cbc, 0)){
		__warnx(TIRPC_DEBUG_FLAG_ERROR,
			"%s: xdr_rdma_svc_reply failed (will set dead)",
			__func__);
		return (XPRT_DIED);
	}
	xdrs->x_op = XDR_ENCODE;

	if (!xdr_reply_encode(xdrs, &req->rq_msg)) {
		__warnx(TIRPC_DEBUG_FLAG_ERROR,
			"%s: xdr_reply_encode failed (will set dead)",
			__func__);
		return (XPRT_DIED);
	}
	xdr_tail_update(xdrs);

	if (req->rq_msg.rm_reply.rp_stat == MSG_ACCEPTED
	 && req->rq_msg.rm_reply.rp_acpt.ar_stat == SUCCESS
	 && req->rq_auth
	 && !SVCAUTH_WRAP(req, xdrs)) {
		__warnx(TIRPC_DEBUG_FLAG_ERROR,
			"%s: SVCAUTH_WRAP failed (will set dead)",
			__func__);
		return (XPRT_DIED);
	}
	xdr_tail_update(xdrs);
#if 1
	if (!xdr_fabric_svc_flushout(cbc)){
		__warnx(TIRPC_DEBUG_FLAG_ERROR,
			"%s: flushout failed (will set dead)",
			__func__);
		return (XPRT_DIED);
	}
#endif

	return (XPRT_IDLE);
}

