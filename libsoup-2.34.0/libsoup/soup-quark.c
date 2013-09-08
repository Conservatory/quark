/* -*- Mode: C; tab-width: 8; indent-tabs-mode: t; c-basic-offset: 8 -*- */

#ifdef HAVE_CONFIG_H
#include <config.h>
#endif

#include <stdio.h>
#include <string.h>
#include <sys/socket.h>
#include <unistd.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <glib.h>
#include <unistd.h>
#include <sys/select.h>
/* According to earlier standards */
#include <sys/time.h>
#include <sys/types.h>

#include "soup-address.h"
#include "soup-cookie.h"
#include "soup-uri.h"
#include "soup-date.h"

#include "soup-quark.h"

int t2k_socket = 0;
int kcookies_flag = 0;

int quarkMsgQueueIdx = -1;
QuarkMessage quarkMsgQueue[QUARK_MSG_QUEUE_SIZE];

void quark_enqueue_msg(char msg_id, char* param) {
	g_assert (param != NULL);

	if(quarkMsgQueueIdx >= QUARK_MSG_QUEUE_SIZE - 1) {
		// we drop a new message when the queue is full.
		return; 
	}
	++quarkMsgQueueIdx;
	quarkMsgQueue[quarkMsgQueueIdx].msg_id = msg_id;
	strncpy(quarkMsgQueue[quarkMsgQueueIdx].param, param, 511);
}	

int quark_queue_idx() {
	return quarkMsgQueueIdx;
}

void quark_dequeue_msg(QuarkMessage* msg) {
	g_assert (msg != NULL);

	if (quarkMsgQueueIdx < 0) {
		msg->msg_id = 0;
		msg->param[0] = 0;
		return;
	}
	--quarkMsgQueueIdx;
	msg->msg_id = quarkMsgQueue[quarkMsgQueueIdx+1].msg_id;
	strncpy(msg->param, quarkMsgQueue[quarkMsgQueueIdx+1].param, 511);
}

// icookies point to a domain of the cookie.
SoupCookieList clist_head = {
	.soup_cookie = NULL,
	.next = NULL
};

SoupCookieList* clist_tail = &clist_head;


void soup_add_invalidated_cookie(const char* cookie) {
	g_assert (cookie != NULL);

	clist_tail = (clist_tail->next = (SoupCookieList*)g_malloc(sizeof(SoupCookieList)));
	clist_tail->next = NULL;
	clist_tail->soup_cookie = soup_cookie_parse(cookie, NULL);

	g_assert (clist_tail->soup_cookie != NULL);

#ifdef PRINT_DBG_MSG
	fprintf(stderr, "soup_add_invalidated_cookie:%s:%d\n",cookie, (int)clist_tail->soup_cookie);
#endif
}

SoupCookieList* soup_get_invalidated_cookies() {
	return clist_head.next;
}

void soup_empty_invalidated_cookies() {
	SoupCookieList* next = NULL;
	SoupCookieList* m_head = NULL;

	m_head = clist_head.next;
	clist_head.next = NULL;
	clist_tail = &clist_head;
	
	while(m_head) {
		next = m_head->next;
		if(m_head->soup_cookie) soup_cookie_free(m_head->soup_cookie);
		g_free(m_head);
		m_head = next;
	}
}

void soup_set_kcookies_flag(int flag) {
	kcookies_flag = flag;
}

int soup_get_kcookies_flag(void) {
	//return kcookies_flag;
	return 1;
}

void soup_set_t2k_raw_socket(int raw_sock) {
	t2k_socket = raw_sock;
}

int soup_get_t2k_raw_socket() {
	return t2k_socket;
}

void write_msg_id_to_kernel (char msg_id) {
	if (write(t2k_socket, &msg_id, 1) != 1) return;
}

unsigned int endian_swap(unsigned int x) {
	x = (x>>24) | ((x<<8) & 0x00FF0000) | ((x>>8) & 0x0000FF00) | (x<<24);
	return x;
}

void write_param_to_kernel (char *param)
{
	unsigned int size = strlen(param);
	unsigned int encoded_size = endian_swap(size);

	g_assert(param != NULL);


#ifdef PRINT_DBG_MSG
	fprintf(stderr, "##soup-quark:write_param_to_kernel:%d\n",size);
	fflush(stderr);
#endif
	if (write(t2k_socket, &encoded_size, 4) != 4) return;
	if (write(t2k_socket, param, size) != size) return;
}

void write_msg_to_kernel(char msg_id,char *param) {
	write_msg_id_to_kernel(msg_id);
	write_param_to_kernel(param);
}

char read_msg_id_from_kernel(void) {
	char c = 0;
	if (read(t2k_socket, &c, 1) != 1) return -1;
	return c;

	/*
	char c = 0;
	//read(t2k_socket, &c, 1);	
	fd_set rfds;
	struct timeval tv;
	int retval;

	FD_ZERO(&rfds);
	FD_SET(t2k_socket, &rfds);
	tv.tv_sec = 3;
	tv.tv_usec = 0;

	retval = select(t2k_socket + 1, &rfds, NULL, NULL, &tv);
	if (retval) {
		read(t2k_socket, &c, 1);	
		return c;
	} else {
		return -1;
	}
	*/
}

void read_param_from_kernel(GString *result) {
	unsigned int size;
	int to_read, did_read, read_so_far;
	char buf[1024];
	int read_char = read(t2k_socket, &size, 4);
	size = endian_swap(size);

	g_assert(result != NULL);

	read_char = read_char;
	//#ifdef PRINT_DBG_MSG
	//fprintf(stderr, "## ] read_param(size) : read_char %d\n", read_char);
	//fprintf(stderr, "## ] read_param(size) : size %d\n", size);
	//fflush(stderr);
	//#endif
	//read(t2k_socket, &size, 4);
	//fprintf(stderr, "## ] 1-read_param : size %d\n", size);	
	read_so_far = 0;
	while (read_so_far < size) {
		to_read = size - read_so_far;
		if (to_read >= 1024) {
			to_read = 1024;
		}
		did_read = read(t2k_socket, buf, to_read);
		if (result) {
			g_string_append_len(result, buf, did_read);
		}
		read_so_far += did_read;
	}

	g_string_append_len(result, "\0", 1);
}

char * read_msg_from_kernel(char msg_id) {
#ifdef PRINT_DBG_MSG
	fprintf(stderr, "## begin] read_msg_from_kernel:%d\n", msg_id);
#endif
	GString *result;
	char* param_ptr = NULL;
	char c;
	c = read_msg_id_from_kernel();

	if (c < 0) {
#ifdef PRINT_DBG_MSG
		fprintf(stderr, "## end] read_msg_from_kernel: socket is failed to be received by timeout\n");
#endif
		return NULL;
	}

#ifdef PRINT_DBG_MSG
	fprintf(stderr, "## midl] read_msg : msg_id : %d, requested one:%d\n", c, msg_id);
#endif
	while(c != msg_id) {
#ifdef PRINT_DBG_MSG
		fprintf(stderr, "## midl] read_msg : loop\n");
#endif
		result = g_string_new (NULL);	
		read_param_from_kernel(result);
		param_ptr = g_string_free (result, FALSE);
		//fprintf(stderr, "## libsoup] message is dropped size: %d\n", strlen(param_ptr));
		//fprintf(stderr, "## libsoup] message is dropped : %d,%d\n", c, tptr[0]);
		//fflush(stderr);		
		quark_enqueue_msg(c, param_ptr);
		g_free(param_ptr);
		
		c = read_msg_id_from_kernel();
#ifdef PRINT_DBG_MSG
		fprintf(stderr, "## midl] read_msg : msg_id : %d\n", c);
#endif
	} 
	result = g_string_new (NULL);
	read_param_from_kernel(result);
#ifdef PRINT_DBG_MSG
	fprintf(stderr, "## end] read_msg_from_kernel\n");
#endif
	// fprintf(stderr, "## read msg length : %d\n",result->len); fflush(stderr);
	fflush(stderr);

	return g_string_free (result, FALSE);
}

char * serialize_cookie_for_kernel (SoupCookie *cookie)
{
	GString *result;

	if (!*cookie->name && !*cookie->value) {
		return NULL;
	}

	result = g_string_new (NULL);
	g_string_append (result, cookie->name);
	g_string_append (result, "=");
	g_string_append (result, cookie->value);

	if (cookie->expires) {
		char *timestamp;

		g_string_append (result, "; expires=");
		timestamp = soup_date_to_string (cookie->expires,
						 SOUP_DATE_COOKIE);
		g_string_append (result, timestamp);
		g_free (timestamp);
	}
	if (cookie->path) {
		g_string_append (result, "; path=");
		g_string_append (result, cookie->path);
	}
	if (cookie->domain) {
		g_string_append (result, "; domain=");
		g_string_append (result, cookie->domain);
	}
	if (cookie->secure)
		g_string_append (result, "; secure=true");
	if (cookie->http_only)
		g_string_append (result, "; httponly=true");

	return g_string_free (result, FALSE);
}

void
send_cookie_to_kernel (SoupCookie *cookie) {
	char* cookie_str;
	cookie_str = serialize_cookie_for_kernel(cookie);
	//soup_add_invalidated_cookie(cookie_str);
	write_msg_to_kernel((char) 11, cookie_str);
	g_free(cookie_str);
}

char *
get_cookies_from_kernel (SoupURI *uri,
			 gboolean for_http) {
	char *request_param;
	char* cookie_from_kernel;
	request_param = g_strdup_printf("%s;%s;%s;%d", uri->scheme, uri->host, uri->path, for_http);
	write_msg_to_kernel((char) 10, request_param);
	g_free(request_param);
	cookie_from_kernel = read_msg_from_kernel((char) 12);
#ifdef PRINT_DBG_MSG
	fprintf(stderr, "## cookie is received from kernel(tab) :%s\n", cookie_from_kernel); fflush(stderr);
#endif
	return cookie_from_kernel;
}


#define CMSG_SIZE CMSG_SPACE(sizeof(int))

int _recvfd(int sock, size_t *len, void *buf) {

#ifdef PRINT_DBG_MSG
	fprintf(stderr, "## begin] recvfd\n"); fflush(stderr);
#endif
	struct iovec iov[1];
	struct msghdr msgh;
	char cmsgbuf[CMSG_SIZE];
	char extrabuf[4096];
	struct cmsghdr *h;
	int st, fd;

	if(*len < 1 || buf == NULL) {
		/* For some reason, again, one byte needs to be received. (it would not
		 * block?) */
		iov[0].iov_base = extrabuf;
		iov[0].iov_len  = sizeof(extrabuf);
	} else {
		iov[0].iov_base = buf;
		iov[0].iov_len  = *len;
	}

	msgh.msg_name       = NULL;
	msgh.msg_namelen    = 0;

	msgh.msg_iov        = iov;
	msgh.msg_iovlen     = 1;

	msgh.msg_control    = cmsgbuf;
	msgh.msg_controllen = CMSG_SIZE;
	msgh.msg_flags      = 0;

#ifdef PRINT_DBG_MSG
	fprintf(stderr, "## midl] recvfd - recvmsg is called\n"); fflush(stderr);
#endif
	st = recvmsg(sock, &msgh, 0);

#ifdef PRINT_DBG_MSG
	fprintf(stderr, "## midl] recvfd - recvmsg is finished\n"); fflush(stderr);
#endif

#ifdef PRINT_DBG_MSG
	fprintf(stderr, "## end] recvfd\n"); fflush(stderr);
#endif

	if(st < 0) {
		return -1;
	}

	*len = st;
	h = CMSG_FIRSTHDR(&msgh);
	/* Check if we received what we expected */
	if((h == NULL)
	   || h->cmsg_len    != CMSG_LEN(sizeof(int))
	   || h->cmsg_level  != SOL_SOCKET
	   || h->cmsg_type   != SCM_RIGHTS) {
		return -2;
	}

	fd = ((int *)CMSG_DATA(h))[0];
	if(fd < 0)
		return -3;
	return fd;
}

int get_socket_from_kernel (const char       *hostname, 
			    int               port,
			    GSocketFamily     family, 
			    int               type,
			    int               protocol) {
	
	char buf[1024];
	char *dummy = NULL;
	size_t len;
	int rsock;

	sprintf(buf, "%s:%d:%d:%d:%d", hostname, port, family, type, protocol);
	write_msg_to_kernel((char) 3, buf);

#ifdef PRINT_DBG_MSG
	fprintf(stderr, "## begin] get_socket_from_kernel\n"); fflush(stderr);
#endif
	dummy = read_msg_from_kernel((char) 8);
	if(dummy == NULL) {
		fprintf(stderr, "FATAL ERROR:libsoup-soup_quark.c] get_socket_from_kernel is failed : timeout\n"); fflush(stderr);
		return -1;
	}

	//fprintf(stderr, "returned dummy : %d\n", *dummy); fflush(stderr);

	if(*dummy != 0) {
		fprintf(stderr, "FATAL ERROR:libsoup-soup-quark.c] get_socket_from_kernel is failed : not the same domain:%s:error code:%s\n", hostname, dummy); fflush(stderr);
		g_free(dummy);
		return -1;
	}

	//fprintf(stderr, "returned dummy :%d %d %d %d\n", dummy[0], dummy[1], dummy[2], dummy[3]);

#ifdef PRINT_DBG_MSG
	fprintf(stderr, "## midl] get_socket_from_kernel:msg is read\n"); fflush(stderr);
#endif
	g_free(dummy);
	len = 0;

#ifdef PRINT_DBG_MSG
	fprintf(stderr, "## midl] get_socket_from_kernel:recvfd is called\n"); fflush(stderr);
#endif
	rsock = _recvfd(t2k_socket, &len, NULL);
	
	struct stat statbuf;
	fstat(rsock, &statbuf);
	if(!S_ISSOCK(statbuf.st_mode)) {
		return -1;
	}

#ifdef PRINT_DBG_MSG
	fprintf(stderr, "## midl] get_socket_from_kernel:recvfd is finished\n"); fflush(stderr);
#endif
	
#ifdef PRINT_DBG_MSG
	fprintf(stderr, "## end] get_socket_from_kernel:%d\n", rsock); fflush(stderr);
#endif
	return rsock;
}


	/* char c; */
	/* c = (char) 13; */
	/* write(t2k_socket, &c, 1); */

	/* char buf[1024]; */
	/* int size = sprintf(buf, "%s:%d:%d:%d:%d", hostname, port, family, type, protocol); */
	/* write(t2k_socket, &size, 4); */
	/* write(t2k_socket, buf, size); */

	/* read(t2k_socket, &c, 1); */
	/* while(c != (char) 14) { */
	/* 	read(t2k_socket, &size, 4); */
	/* 	  int read_so_far = 0; */
	/* 	  while (read_so_far < size) { */
	/* 		  int to_read = size - read_so_far; */
	/* 		  if (to_read >= 1024) { */
	/* 			  to_read = 1024; */
	/* 		  } */
	/* 		  read_so_far += read(t2k_socket, buf, to_read); */
	/* 	  } */
	/* 	  read(t2k_socket, &c, 1); */
	/*   }  */

	/*   // time to read the payload - file desciptor. */
	/*   size_t len = 0; */
	/*   int socket_fd = _recvfd(t2k_socket, &len, NULL); */




	  /* char buf[256]; */
	  /* memset(buf, 0, 256); */
	  /* int written_size = 0; */
	  /* written_size = sprintf(buf, "RequestSocket"); */
	  /* write(t2k_socket, buf, written_size + 1); */

	  /* written_size = sprintf(buf, "%s:%d:%d:%d:%d", hostname, port, family, type, protocol); */
	  /* write(t2k_socket, buf, written_size + 1); */
	  
	  // busy wait to get the right message tag
/* 	  do { */
/* 		  int buf_cnt = -1; */
/* 		  memset(buf, 0, 256); */
/* 		  do { */
/* 			  ++buf_cnt; */
/* 			  read(t2k_socket, &(buf[buf_cnt]), 1); */
/* 		  } while (buf[buf_cnt] != 0); */
/* #ifdef PRINT_DBG_MSG */
/* 		  fprintf(stderr, "received tag=[%s]",buf); */
/* #endif */
/* 	  } while(strcmp(buf, "ResultSocket") != 0); */
	  
