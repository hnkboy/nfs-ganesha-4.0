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

#include <rdma/fi_errno.h>
#include <rdma/fi_cm.h>
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

static struct xp_ops rpc_fabric_ops;

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


static int post_recv(void *buf, ssize_t size)
{
	int ret;
	do {
		ret = fi_recv(ep, buf, size, mr, remote_fi_addr, NULL);
		if (ret && ret != -FI_EAGAIN) {
			printf("error posting recv buffer (%d\n", ret);
			return ret;
		}
		if (ret == -FI_EAGAIN)
			(void) fi_cq_read(rxcq, NULL, 0);
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

	return 0;
}


static int start_server(void)
{
	int ret = -1;
	char *service_port = "9228";

	ret = fi_getinfo(FI_VERSION(1,20), NULL, service_port, FI_SOURCE, hints, &fi_pep);
	if (ret) {
		printf("fi_getinfo error (%d)\n", ret);
		return ret;
	}
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

	rd = fi_eq_sread(eq, &event, &entry, sizeof(entry), -1, 0); // 等待读取客户端触发的服务端事件, 读取事件, 推动进展(驱动程序运转)
	if (rd != sizeof(entry)) {
		ret = (int) rd;
		printf("fi_eq_sread: %d", ret);
		if (ret)
			goto err;
	}
	fi = entry.info;                            // info赋值到fi,后续操作的fi都是这个连接后的
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

#if 0
	ret = alloc_msgs();
	if (ret){
		printf("ft_alloc_msgs: %d", ret);
		return ret;
	}
#endif



	ret = fi_accept(ep, NULL, 0);
	if (ret) {
		printf("fi_accept: %d\n", ret);
		return ret;
	}
	printf("fi_accept: %d\n", ret);
	rd = fi_eq_sread(eq, &event, &entry, sizeof(entry), -1, 0);
	if (rd != sizeof(entry)) {
		ret = (int) rd;
		printf("fi_eq_read: %d\n", ret);
		return ret;
	}
	printf("fi_eq_read: %d\n", ret);
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
xdr_fabric_create_ioq(RDMAXPRT *xd)
{
	uint8_t *b;

	if (!xd->pd || !xd->pd->pd) {
		__warnx(TIRPC_DEBUG_FLAG_ERROR,
			"%s() %p[%u] missing Protection Domain",
			__func__, xd, xd->state);
		return ENODEV;
	}

	/* pre-allocated buffer_total:
	 * the number of credits is irrelevant here.
	 * instead, allocate buffers to match the read/write contexts.
	 * more than one buffer can be chained to one ioq_uv head,
	 * but never need more ioq_uv heads than buffers.
	 */
	xd->buffer_total = xd->sm_dr.recvsz * xd->xa->rq_depth
			 + xd->sm_dr.sendsz * xd->xa->sq_depth;

	xd->buffer_aligned = mem_aligned(xd->sm_dr.pagesz, xd->buffer_total);

	__warnx(TIRPC_DEBUG_FLAG_ERROR,
	"%s() buffer_aligned at %p, pagesz %d, buffer_total %d, ",
		__func__, xd->buffer_aligned);

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

	//while (xd->sm_dr.ioq.ioq_uv.uvqh.qcount < CALLQ_SIZE) {
	//	xdr_rdma_callq(xd);
	//}
	return 0;
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

	//dst_addr = argv[1];
	hints->ep_attr->type = FI_EP_MSG; // 可靠数据报端点, 类似socket, 但无须执行listen/connect/accept
	hints->caps = FI_MSG;
 	hints->fabric_attr->prov_name = "verbs";
	hints->addr_format = 0;
	hints->tx_attr->op_flags = FI_DELIVERY_COMPLETE;
	hints->tx_attr->tclass = 513;
	hints->domain_attr->threading = FI_THREAD_DOMAIN;
	hints->domain_attr->mr_mode = FI_MR_LOCAL | FI_MR_ENDPOINT | OFI_MR_BASIC_MAP | FI_MR_RAW;
	hints->tx_attr->op_flags = 0;

	rc = start_server();
	__warnx(TIRPC_DEBUG_FLAG_ERROR,
			"%s() NFS/FABRIC start server, rc=%d.", __func__, rc);
	if (rc) {
		return NULL;
	}
	rc = xdr_fabric_create_ioq(xd);
	__warnx(TIRPC_DEBUG_FLAG_ERROR,
			"%s() NFS/FABRIC create ioq, rc=%d.", __func__,rc);
	if (rc) {
		return NULL;
	}
	rc = server_connect(xd);
	__warnx(TIRPC_DEBUG_FLAG_ERROR,
			"%s() NFS/FABRIC start server, rc=%d.", __func__, rc);
	if (rc) {
		return NULL;
	}

	rc = post_recv(xd->buffer_aligned, xd->sm_dr.sendsz);
	if (!rc) {
		wait_recvcq();
	}
	else {
		__warnx(TIRPC_DEBUG_FLAG_ERROR,
				"%s() NFS/FABRIC  post recv faild, rc=%d.", __func__, rc);

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

/*
 * svc_rdma_rendezvous: waits for connection request
 */
enum xprt_stat
svc_fabric_rendezvous(SVCXPRT *xprt)
{
	return (XPRT_IDLE);
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


static struct xp_ops rpc_fabric_ops = {
	.xp_recv = svc_fabric_rendezvous,
	.xp_stat = svc_rendezvous_stat,
	.xp_decode = (svc_req_fun_t)abort,
	.xp_reply = (svc_req_fun_t)abort,
	.xp_checksum = NULL,		/* not used */
	.xp_unlink = rpc_fabric_unlink_it,
	.xp_destroy = rpc_fabric_destroy_it,
	.xp_control = rpc_fabric_control,
	.xp_free_user_data = NULL,	/* no default */
};






