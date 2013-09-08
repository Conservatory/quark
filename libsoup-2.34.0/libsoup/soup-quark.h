/* -*- Mode: C; tab-width: 8; indent-tabs-mode: t; c-basic-offset: 8 -*- */

#ifndef SOUP_QUARK_H
#define SOUP_QUARK_H 1

#define QUARK_MSG_QUEUE_SIZE 16
#define QUARK_MSG_PARAM_SIZE 512

G_BEGIN_DECLS

struct SoupCookieListRec {
	SoupCookie* soup_cookie;
	struct SoupCookieListRec* next;
};

typedef struct SoupCookieListRec SoupCookieList;


struct _QuarkMessage {
	char msg_id;
	char param[QUARK_MSG_PARAM_SIZE];	
};
typedef struct _QuarkMessage QuarkMessage;

void quark_enqueue_msg(char msg_id, char* param) ;

int quark_queue_idx(void);

void quark_dequeue_msg(QuarkMessage* msg);

void  soup_add_invalidated_cookie(const char* cookie) ;

SoupCookieList* soup_get_invalidated_cookies(void);

void soup_empty_invalidated_cookies(void);

void           soup_set_t2k_raw_socket        (int raw_sock);
int            soup_get_t2k_raw_socket        (void);

void send_cookie_to_kernel                    (SoupCookie *cookie);

char *get_cookies_from_kernel                 (SoupURI          *uri,
					       gboolean          for_http);

int get_socket_from_kernel                    (const char        *hostname, 
					       int               port,
					       GSocketFamily     family, 
					       int               type,
					       int               protocol);

void soup_set_kcookies_flag(int flag);

int soup_get_kcookies_flag(void);

void write_msg_id_to_kernel (char msg_id);

unsigned int endian_swap(unsigned int x);

void write_param_to_kernel (char *param);

void write_msg_to_kernel(char msg_id,char *param);

void read_param_from_kernel(GString *result);

char * read_msg_from_kernel(char msg_id);

char read_msg_id_from_kernel(void);

char * serialize_cookie_for_kernel (SoupCookie *cookie);

int _recvfd(int sock, size_t *len, void *buf);

G_END_DECLS

#endif
