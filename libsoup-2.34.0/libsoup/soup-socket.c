/* -*- Mode: C; tab-width: 8; indent-tabs-mode: t; c-basic-offset: 8 -*- */
/*
 * soup-socket.c: Socket networking code.
 *
 * Copyright (C) 2000-2003, Ximian, Inc.
 */

#ifdef HAVE_CONFIG_H
#include <config.h>
#endif

#include <sys/socket.h>
#include <sys/types.h>

#include <stdio.h>
#include <errno.h>
#include <fcntl.h>
#include <signal.h>
#include <string.h>
#include <unistd.h>

#include "soup-address.h"
#include "soup-socket.h"
#include "soup-marshal.h"
#include "soup-misc.h"
#include "soup-ssl.h"
#include "soup-quark.h"

/**
 * SECTION:soup-socket
 * @short_description: A network socket
 *
 * #SoupSocket is libsoup's TCP socket type. While it is primarily
 * intended for internal use, #SoupSocket<!-- -->s are exposed in the
 * API in various places, and some of their methods (eg,
 * soup_socket_get_remote_address()) may be useful to applications.
 **/

G_DEFINE_TYPE (SoupSocket, soup_socket, G_TYPE_OBJECT)

enum {
	READABLE,
	WRITABLE,
	DISCONNECTED,
	NEW_CONNECTION,
	LAST_SIGNAL
};

static guint signals[LAST_SIGNAL] = { 0 };

enum {
	PROP_0,

	PROP_LOCAL_ADDRESS,
	PROP_REMOTE_ADDRESS,
	PROP_NON_BLOCKING,
	PROP_IS_SERVER,
	PROP_SSL_CREDENTIALS,
	PROP_SSL_STRICT,
	PROP_ASYNC_CONTEXT,
	PROP_TIMEOUT,
	PROP_TRUSTED_CERTIFICATE,
	PROP_CLEAN_DISPOSE,
	PROP_TLS_CERTIFICATE,
	PROP_TLS_ERRORS,

	LAST_PROP
};

typedef struct {
	SoupAddress *local_addr, *remote_addr;
	GIOStream *conn;
	GSocket *gsock;
	GPollableInputStream *istream;
	GPollableOutputStream *ostream;
	GTlsCertificateFlags tls_errors;

	guint non_blocking:1;
	guint is_server:1;
	guint ssl_strict:1;
	guint ssl_ca_in_creds:1;
	guint clean_dispose:1;
	gpointer ssl_creds;

	GMainContext   *async_context;
	GSource        *watch_src;
	GSource        *read_src, *write_src;
	GByteArray     *read_buf;

	GMutex *iolock, *addrlock;
	guint timeout;

	GCancellable *connect_cancel;
} SoupSocketPrivate;
#define SOUP_SOCKET_GET_PRIVATE(o) (G_TYPE_INSTANCE_GET_PRIVATE ((o), SOUP_TYPE_SOCKET, SoupSocketPrivate))

static void set_property (GObject *object, guint prop_id,
			  const GValue *value, GParamSpec *pspec);
static void get_property (GObject *object, guint prop_id,
			  GValue *value, GParamSpec *pspec);

static void soup_socket_peer_certificate_changed (GObject *conn,
						  GParamSpec *pspec,
						  gpointer user_data);

static void
soup_socket_init (SoupSocket *sock)
{
	SoupSocketPrivate *priv = SOUP_SOCKET_GET_PRIVATE (sock);

	priv->non_blocking = TRUE;
	priv->addrlock = g_mutex_new ();
	priv->iolock = g_mutex_new ();
}

static void
disconnect_internal (SoupSocket *sock)
{
	SoupSocketPrivate *priv = SOUP_SOCKET_GET_PRIVATE (sock);

	if (priv->gsock) {
		g_socket_close (priv->gsock, NULL);
		g_object_unref (priv->gsock);
		priv->gsock = NULL;
	}
	if (priv->conn) {
		if (G_IS_TLS_CONNECTION (priv->conn))
			g_signal_handlers_disconnect_by_func (priv->conn, soup_socket_peer_certificate_changed, sock);
		g_object_unref (priv->conn);
		priv->conn = NULL;
		priv->istream = NULL;
		priv->ostream = NULL;
	}

	if (priv->read_src) {
		g_source_destroy (priv->read_src);
		priv->read_src = NULL;
	}
	if (priv->write_src) {
		g_source_destroy (priv->write_src);
		priv->write_src = NULL;
	}
}

static void
finalize (GObject *object)
{
	//printf("soup_socket_finalize\n");
	SoupSocketPrivate *priv = SOUP_SOCKET_GET_PRIVATE (object);

	if (priv->connect_cancel) {
		if (priv->clean_dispose)
			g_warning ("Disposing socket %p during connect", object);
		g_object_unref (priv->connect_cancel);
	}
	if (priv->conn) {
		if (priv->clean_dispose)
			g_warning ("Disposing socket %p while still connected", object);
		disconnect_internal (SOUP_SOCKET (object));
	}

	if (priv->local_addr)
		g_object_unref (priv->local_addr);
	if (priv->remote_addr)
		g_object_unref (priv->remote_addr);

	if (priv->watch_src) {
		if (priv->clean_dispose && !priv->is_server)
			g_warning ("Disposing socket %p during async op", object);
		g_source_destroy (priv->watch_src);
	}
	if (priv->async_context)
		g_main_context_unref (priv->async_context);

	if (priv->read_buf)
		g_byte_array_free (priv->read_buf, TRUE);

	g_mutex_free (priv->addrlock);
	g_mutex_free (priv->iolock);

	G_OBJECT_CLASS (soup_socket_parent_class)->finalize (object);
}

static void
soup_socket_class_init (SoupSocketClass *socket_class)
{
	//printf("soup_socket_class_init\n");


	GObjectClass *object_class = G_OBJECT_CLASS (socket_class);

	g_type_class_add_private (socket_class, sizeof (SoupSocketPrivate));

	/* virtual method override */
	object_class->finalize = finalize;
	object_class->set_property = set_property;
	object_class->get_property = get_property;

	/* signals */

	/**
	 * SoupSocket::readable:
	 * @sock: the socket
	 *
	 * Emitted when an async socket is readable. See
	 * soup_socket_read(), soup_socket_read_until() and
	 * #SoupSocket:non-blocking.
	 **/
	signals[READABLE] =
		g_signal_new ("readable",
			      G_OBJECT_CLASS_TYPE (object_class),
			      G_SIGNAL_RUN_LAST,
			      G_STRUCT_OFFSET (SoupSocketClass, readable),
			      NULL, NULL,
			      soup_marshal_NONE__NONE,
			      G_TYPE_NONE, 0);

	/**
	 * SoupSocket::writable:
	 * @sock: the socket
	 *
	 * Emitted when an async socket is writable. See
	 * soup_socket_write() and #SoupSocket:non-blocking.
	 **/
	signals[WRITABLE] =
		g_signal_new ("writable",
			      G_OBJECT_CLASS_TYPE (object_class),
			      G_SIGNAL_RUN_LAST,
			      G_STRUCT_OFFSET (SoupSocketClass, writable),
			      NULL, NULL,
			      soup_marshal_NONE__NONE,
			      G_TYPE_NONE, 0);

	/**
	 * SoupSocket::disconnected:
	 * @sock: the socket
	 *
	 * Emitted when the socket is disconnected, for whatever
	 * reason.
	 **/
	signals[DISCONNECTED] =
		g_signal_new ("disconnected",
			      G_OBJECT_CLASS_TYPE (object_class),
			      G_SIGNAL_RUN_LAST,
			      G_STRUCT_OFFSET (SoupSocketClass, disconnected),
			      NULL, NULL,
			      soup_marshal_NONE__NONE,
			      G_TYPE_NONE, 0);

	/**
	 * SoupSocket::new-connection:
	 * @sock: the socket
	 * @new: the new socket
	 *
	 * Emitted when a listening socket (set up with
	 * soup_socket_listen()) receives a new connection.
	 *
	 * You must ref the @new if you want to keep it; otherwise it
	 * will be destroyed after the signal is emitted.
	 **/
	signals[NEW_CONNECTION] =
		g_signal_new ("new_connection",
			      G_OBJECT_CLASS_TYPE (object_class),
			      G_SIGNAL_RUN_FIRST,
			      G_STRUCT_OFFSET (SoupSocketClass, new_connection),
			      NULL, NULL,
			      soup_marshal_NONE__OBJECT,
			      G_TYPE_NONE, 1,
			      SOUP_TYPE_SOCKET);

	/* properties */
	/**
	 * SOUP_SOCKET_LOCAL_ADDRESS:
	 *
	 * Alias for the #SoupSocket:local-address property. (Address
	 * of local end of socket.)
	 **/
	g_object_class_install_property (
		object_class, PROP_LOCAL_ADDRESS,
		g_param_spec_object (SOUP_SOCKET_LOCAL_ADDRESS,
				     "Local address",
				     "Address of local end of socket",
				     SOUP_TYPE_ADDRESS,
				     G_PARAM_READWRITE | G_PARAM_CONSTRUCT_ONLY));
	/**
	 * SOUP_SOCKET_REMOTE_ADDRESS:
	 *
	 * Alias for the #SoupSocket:remote-address property. (Address
	 * of remote end of socket.)
	 **/
	g_object_class_install_property (
		object_class, PROP_REMOTE_ADDRESS,
		g_param_spec_object (SOUP_SOCKET_REMOTE_ADDRESS,
				     "Remote address",
				     "Address of remote end of socket",
				     SOUP_TYPE_ADDRESS,
				     G_PARAM_READWRITE | G_PARAM_CONSTRUCT_ONLY));
	/**
	 * SoupSocket:non-blocking:
	 *
	 * Whether or not the socket uses non-blocking I/O.
	 *
	 * #SoupSocket's I/O methods are designed around the idea of
	 * using a single codepath for both synchronous and
	 * asynchronous I/O. If you want to read off a #SoupSocket,
	 * the "correct" way to do it is to call soup_socket_read() or
	 * soup_socket_read_until() repeatedly until you have read
	 * everything you want. If it returns %SOUP_SOCKET_WOULD_BLOCK
	 * at any point, stop reading and wait for it to emit the
	 * #SoupSocket::readable signal. Then go back to the
	 * reading-as-much-as-you-can loop. Likewise, for writing to a
	 * #SoupSocket, you should call soup_socket_write() either
	 * until you have written everything, or it returns
	 * %SOUP_SOCKET_WOULD_BLOCK (in which case you wait for
	 * #SoupSocket::writable and then go back into the loop).
	 *
	 * Code written this way will work correctly with both
	 * blocking and non-blocking sockets; blocking sockets will
	 * simply never return %SOUP_SOCKET_WOULD_BLOCK, and so the
	 * code that handles that case just won't get used for them.
	 **/
	/**
	 * SOUP_SOCKET_FLAG_NONBLOCKING:
	 *
	 * Alias for the #SoupSocket:non-blocking property. (Whether
	 * or not the socket uses non-blocking I/O.)
	 **/
	g_object_class_install_property (
		object_class, PROP_NON_BLOCKING,
		g_param_spec_boolean (SOUP_SOCKET_FLAG_NONBLOCKING,
				      "Non-blocking",
				      "Whether or not the socket uses non-blocking I/O",
				      TRUE,
				      G_PARAM_READWRITE));
	/**
	 * SOUP_SOCKET_IS_SERVER:
	 *
	 * Alias for the #SoupSocket:is-server property. (Whether or
	 * not the socket is a server socket.)
	 **/
	g_object_class_install_property (
		object_class, PROP_IS_SERVER,
		g_param_spec_boolean (SOUP_SOCKET_IS_SERVER,
				      "Server",
				      "Whether or not the socket is a server socket",
				      FALSE,
				      G_PARAM_READABLE));
	/**
	 * SOUP_SOCKET_SSL_CREDENTIALS:
	 *
	 * Alias for the #SoupSocket:ssl-credentials property.
	 * (SSL credential information.)
	 **/
	g_object_class_install_property (
		object_class, PROP_SSL_CREDENTIALS,
		g_param_spec_pointer (SOUP_SOCKET_SSL_CREDENTIALS,
				      "SSL credentials",
				      "SSL credential information, passed from the session to the SSL implementation",
				      G_PARAM_READWRITE));
	/**
	 * SOUP_SOCKET_SSL_STRICT:
	 *
	 * Alias for the #SoupSocket:ignore-ssl-cert-errors property.
	 **/
	g_object_class_install_property (
		object_class, PROP_SSL_STRICT,
		g_param_spec_boolean (SOUP_SOCKET_SSL_STRICT,
				      "Strictly validate SSL certificates",
				      "Whether certificate errors should be considered a connection error",
				      TRUE,
				      G_PARAM_READWRITE | G_PARAM_CONSTRUCT_ONLY));
	/**
	 * SOUP_SOCKET_TRUSTED_CERTIFICATE:
	 *
	 * Alias for the #SoupSocket:trusted-certificate
	 * property.
	 **/
	g_object_class_install_property (
		object_class, PROP_TRUSTED_CERTIFICATE,
		g_param_spec_boolean (SOUP_SOCKET_TRUSTED_CERTIFICATE,
				     "Trusted Certificate",
				     "Whether the server certificate is trusted, if this is an SSL socket",
				     FALSE,
				     G_PARAM_READABLE));
	/**
	 * SOUP_SOCKET_ASYNC_CONTEXT:
	 *
	 * Alias for the #SoupSocket:async-context property. (The
	 * socket's #GMainContext.)
	 **/
	g_object_class_install_property (
		object_class, PROP_ASYNC_CONTEXT,
		g_param_spec_pointer (SOUP_SOCKET_ASYNC_CONTEXT,
				      "Async GMainContext",
				      "The GMainContext to dispatch this socket's async I/O in",
				      G_PARAM_READWRITE | G_PARAM_CONSTRUCT_ONLY));

	/**
	 * SOUP_SOCKET_TIMEOUT:
	 *
	 * Alias for the #SoupSocket:timeout property. (The timeout
	 * in seconds for blocking socket I/O operations.)
	 **/
	g_object_class_install_property (
		object_class, PROP_TIMEOUT,
		g_param_spec_uint (SOUP_SOCKET_TIMEOUT,
				   "Timeout value",
				   "Value in seconds to timeout a blocking I/O",
				   0, G_MAXUINT, 0,
				   G_PARAM_READWRITE));

	g_object_class_install_property (
		object_class, PROP_CLEAN_DISPOSE,
		g_param_spec_boolean ("clean-dispose",
				      "Clean dispose",
				      "Warn on unclean dispose",
				      FALSE,
				      G_PARAM_WRITABLE | G_PARAM_CONSTRUCT_ONLY));
	/**
	 * SOUP_SOCKET_TLS_CERTIFICATE:
	 *
	 * Alias for the #SoupSocket:tls-certificate
	 * property. Note that this property's value is only useful
	 * if the socket is for a TLS connection, and only reliable
	 * after some data has been transferred to or from it.
	 *
	 * Since: 2.34
	 **/
	g_object_class_install_property (
		object_class, PROP_TLS_CERTIFICATE,
		g_param_spec_object (SOUP_SOCKET_TLS_CERTIFICATE,
				     "TLS certificate",
				     "The peer's TLS certificate",
				     G_TYPE_TLS_CERTIFICATE,
				     G_PARAM_READABLE));
	/**
	 * SOUP_SOCKET_TLS_ERRORS:
	 *
	 * Alias for the #SoupSocket:tls-errors
	 * property. Note that this property's value is only useful
	 * if the socket is for a TLS connection, and only reliable
	 * after some data has been transferred to or from it.
	 *
	 * Since: 2.34
	 **/
	g_object_class_install_property (
		object_class, PROP_TLS_ERRORS,
		g_param_spec_flags (SOUP_SOCKET_TLS_ERRORS,
				    "TLS errors",
				    "Errors with the peer's TLS certificate",
				    G_TYPE_TLS_CERTIFICATE_FLAGS, 0,
				    G_PARAM_READABLE));
}


static void
finish_socket_setup (SoupSocketPrivate *priv)
{
	if (!priv->gsock)
		return;

	if (!priv->conn)
		priv->conn = (GIOStream *)g_socket_connection_factory_create_connection (priv->gsock);
	if (!priv->istream)
		priv->istream = G_POLLABLE_INPUT_STREAM (g_io_stream_get_input_stream (priv->conn));
	if (!priv->ostream)
		priv->ostream = G_POLLABLE_OUTPUT_STREAM (g_io_stream_get_output_stream (priv->conn));

	g_socket_set_timeout (priv->gsock, priv->timeout);
}

static void
set_property (GObject *object, guint prop_id,
	      const GValue *value, GParamSpec *pspec)
{
	SoupSocketPrivate *priv = SOUP_SOCKET_GET_PRIVATE (object);

	switch (prop_id) {
	case PROP_LOCAL_ADDRESS:
		priv->local_addr = (SoupAddress *)g_value_dup_object (value);
		break;
	case PROP_REMOTE_ADDRESS:
		priv->remote_addr = (SoupAddress *)g_value_dup_object (value);
		break;
	case PROP_NON_BLOCKING:
		priv->non_blocking = g_value_get_boolean (value);
		break;
	case PROP_SSL_CREDENTIALS:
		priv->ssl_creds = g_value_get_pointer (value);
		break;
	case PROP_SSL_STRICT:
		priv->ssl_strict = g_value_get_boolean (value);
		break;
	case PROP_ASYNC_CONTEXT:
		priv->async_context = g_value_get_pointer (value);
		if (priv->async_context)
			g_main_context_ref (priv->async_context);
		break;
	case PROP_TIMEOUT:
		priv->timeout = g_value_get_uint (value);
		if (priv->conn)
			g_socket_set_timeout (priv->gsock, priv->timeout);
		break;
	case PROP_CLEAN_DISPOSE:
		priv->clean_dispose = g_value_get_boolean (value);
		break;
	default:
		G_OBJECT_WARN_INVALID_PROPERTY_ID (object, prop_id, pspec);
		break;
	}
}

static void
get_property (GObject *object, guint prop_id,
	      GValue *value, GParamSpec *pspec)
{
	SoupSocketPrivate *priv = SOUP_SOCKET_GET_PRIVATE (object);

	switch (prop_id) {
	case PROP_LOCAL_ADDRESS:
		g_value_set_object (value, soup_socket_get_local_address (SOUP_SOCKET (object)));
		break;
	case PROP_REMOTE_ADDRESS:
		g_value_set_object (value, soup_socket_get_remote_address (SOUP_SOCKET (object)));
		break;
	case PROP_NON_BLOCKING:
		g_value_set_boolean (value, priv->non_blocking);
		break;
	case PROP_IS_SERVER:
		g_value_set_boolean (value, priv->is_server);
		break;
	case PROP_SSL_CREDENTIALS:
		g_value_set_pointer (value, priv->ssl_creds);
		break;
	case PROP_SSL_STRICT:
		g_value_set_boolean (value, priv->ssl_strict);
		break;
	case PROP_TRUSTED_CERTIFICATE:
		g_value_set_boolean (value, priv->tls_errors == 0);
		break;
	case PROP_ASYNC_CONTEXT:
		g_value_set_pointer (value, priv->async_context ? g_main_context_ref (priv->async_context) : NULL);
		break;
	case PROP_TIMEOUT:
		g_value_set_uint (value, priv->timeout);
		break;
	case PROP_TLS_CERTIFICATE:
		if (G_IS_TLS_CONNECTION (priv->conn))
			g_value_set_object (value, g_tls_connection_get_peer_certificate (G_TLS_CONNECTION (priv->conn)));
		else
			g_value_set_object (value, NULL);
		break;
	case PROP_TLS_ERRORS:
		g_value_set_flags (value, priv->tls_errors);
		break;
	default:
		G_OBJECT_WARN_INVALID_PROPERTY_ID (object, prop_id, pspec);
		break;
	}
}


/**
 * soup_socket_new:
 * @optname1: name of first property to set (or %NULL)
 * @...: value of @optname1, followed by additional property/value pairs
 *
 * Creates a new (disconnected) socket
 *
 * Return value: the new socket
 **/
SoupSocket *
soup_socket_new (const char *optname1, ...)
{
	SoupSocket *sock;
	va_list ap;

	va_start (ap, optname1);
	sock = (SoupSocket *)g_object_new_valist (SOUP_TYPE_SOCKET,
						  optname1, ap);
	va_end (ap);

	return sock;
}

static guint
socket_connected (SoupSocket *sock, GSocketConnection *conn, GError *error)
{
	SoupSocketPrivate *priv = SOUP_SOCKET_GET_PRIVATE (sock);

	g_object_unref (priv->connect_cancel);
	priv->connect_cancel = NULL;

	if (error) {
		if (error->domain == G_RESOLVER_ERROR) {
			g_error_free (error);
			return SOUP_STATUS_CANT_RESOLVE;
		} else {
			g_error_free (error);
			return SOUP_STATUS_CANT_CONNECT;
		}
	}

	priv->conn = (GIOStream *)conn;
	priv->gsock = g_object_ref (g_socket_connection_get_socket (conn));
	finish_socket_setup (priv);

	return SOUP_STATUS_OK;
}

/**
 * SoupSocketCallback:
 * @sock: the #SoupSocket
 * @status: an HTTP status code indicating success or failure
 * @user_data: the data passed to soup_socket_connect_async()
 *
 * The callback function passed to soup_socket_connect_async().
 **/

typedef struct {
	SoupSocket *sock;
	SoupSocketCallback callback;
	gpointer user_data;
} SoupSocketAsyncConnectData;

static void
async_connected (GObject *client, GAsyncResult *result, gpointer data)
{
	SoupSocketAsyncConnectData *sacd = data;
	SoupSocketPrivate *priv = SOUP_SOCKET_GET_PRIVATE (sacd->sock);
	GError *error = NULL;
	GSocketConnection *conn;
	guint status;

	if (priv->async_context)
		g_main_context_pop_thread_default (priv->async_context);

	conn = g_socket_client_connect_finish (G_SOCKET_CLIENT (client),
					       result, &error);
	status = socket_connected (sacd->sock, conn, error);

	sacd->callback (sacd->sock, status, sacd->user_data);
	g_object_unref (sacd->sock);
	g_slice_free (SoupSocketAsyncConnectData, sacd);
}

/**
 * soup_socket_connect_async:
 * @sock: a client #SoupSocket (which must not already be connected)
 * @cancellable: a #GCancellable, or %NULL
 * @callback: (scope async): callback to call after connecting
 * @user_data: data to pass to @callback
 *
 * Begins asynchronously connecting to @sock's remote address. The
 * socket will call @callback when it succeeds or fails (but not
 * before returning from this function).
 *
 * If @cancellable is non-%NULL, it can be used to cancel the
 * connection. @callback will still be invoked in this case, with a
 * status of %SOUP_STATUS_CANCELLED.
 **/

void
soup_socket_connect_async (SoupSocket *sock, GCancellable *cancellable,
			   SoupSocketCallback callback, gpointer user_data)
{
	SoupSocketPrivate *priv;
	SoupSocketAsyncConnectData *sacd;
	GSocketClient *client;

	g_return_if_fail (SOUP_IS_SOCKET (sock));
	priv = SOUP_SOCKET_GET_PRIVATE (sock);
	g_return_if_fail (priv->remote_addr != NULL);

	sacd = g_slice_new0 (SoupSocketAsyncConnectData);
	sacd->sock = g_object_ref (sock);
	sacd->callback = callback;
	sacd->user_data = user_data;

	priv->connect_cancel = cancellable ? g_object_ref (cancellable) : g_cancellable_new ();

	if (priv->async_context)
		g_main_context_push_thread_default (priv->async_context);

	client = g_socket_client_new ();
	if (priv->timeout)
		g_socket_client_set_timeout (client, priv->timeout);
	g_socket_client_connect_async (client,
				       G_SOCKET_CONNECTABLE (priv->remote_addr),
				       priv->connect_cancel,
				       async_connected, sacd);
	g_object_unref (client);
}


/*
  DON:INFO: indirect socket creation support
*/
static GSocket *
create_connected_socket_thru_kernel (GSocketClient* client,
				     GSocketConnectable  *connectable,
				     GSocketAddress *dest_address,
				     GError        **error)
{
  GSocketFamily family;
  GSocket *gsocket;
  int type;
  int protocol;
  const char *hostname;
  int port;
  int t2k_socket;
  int socket_fd;
	  
  family = g_socket_client_get_family(client);
  if (family == G_SOCKET_FAMILY_INVALID &&
      g_socket_client_get_local_address(client) != NULL)
	  family = g_socket_address_get_family (g_socket_client_get_local_address(client));

  if (family == G_SOCKET_FAMILY_INVALID) {
	  //family = g_socket_address_get_family (dest_address);
	  family = G_SOCKET_FAMILY_IPV4;
  }

  // DON:INFO: the arguments needed to create a socket.
  // family : enum
  // type : enum
  // address: http://developer.gnome.org/gio/2.28/GSocketAddress.html#g-socket-address-to-native
  //  -> native struct sockaddr
  type = g_socket_client_get_socket_type(client);
  protocol = g_socket_client_get_protocol(client);

#ifdef PRINT_DBG_MSG
  fprintf(stderr, "create_connected_socket_thru_kernel]]socket is created\n");
  fprintf(stderr, "create_connected_socket_thru_kernel]]family :%d\n", family); // AF_INET
  fprintf(stderr, "create_connected_socket_thru_kernel]]type :%d\n", type); // SOCK_STREAM
  fprintf(stderr, "create_connected_socket_thru_kernel]]protocol :%d\n", protocol); 
#endif

  // DON:INFO: sockaddr is obtained here but ignored.
  //struct sockaddr addr;
  //g_socket_address_to_native(dest_address, (gpointer)&addr, sizeof(addr), NULL);

  // DON:Q: the sockaddr is really the same as the ip address
  // obtainted from this pair of hostname and port
  hostname = soup_address_get_name(SOUP_ADDRESS(connectable));
  port = soup_address_get_port(SOUP_ADDRESS(connectable));

  t2k_socket = soup_get_t2k_raw_socket();

  if(t2k_socket == 0) {
	  //#ifdef PRINT_DBG_MSG
	  //fprintf(stderr, "_t2k_raw_socket is not yet set:the socket is created by webkit\n");
	  //#endif
	  gsocket = g_socket_new (family,
				  g_socket_client_get_socket_type(client),
				  g_socket_client_get_protocol(client),
				  error);	  
  } else {
	  // send the request message to the kernel
	  socket_fd = get_socket_from_kernel(hostname, port, family, type, protocol);

	  //fprintf(stderr, "]] soup-socket :: returned file descriptor : %d\n", socket_fd); fflush(stderr);
	  if(socket_fd <= 0) {
#ifdef PRINT_DBG_MSG
		  fprintf(stderr, "]] soup-socket: get_socket_from_kernel returns -1: socket creation is failed\n");
#endif
		  g_set_error_literal (error, G_IO_ERROR, G_IO_ERROR_FAILED, ("Unknown error on connect"));
		  return NULL;
	  }
	  gsocket = g_socket_new_from_fd(socket_fd, error);	  
	  	  		  
	  /*
	    old message format
	  write(t2k_socket, &family, sizeof(int));
	  write(t2k_socket, &type, sizeof(int));
	  write(t2k_socket, &protocol, sizeof(int));
	  write(t2k_socket, &port, sizeof(int));
	  write(t2k_socket, hostname, strlen(hostname));
	  
	  int len = 0;
	  int socket_fd = _recvfd(t2k_socket, &len, NULL);
	  gsocket = g_socket_new_from_fd(socket_fd, error);	  
	  */
  }
  //unsigned char socket_request_msg = 10;
  /*
  // msg id
  write(t2k_socket, &socket_request_msg, sizeof(socket_request_msg));
  // payload size
  int payload_size = strlen(hostname) + 1 + sizeof(int);
  write(t2k_socket, &payload_size, sizeof(payload_size));
  */
  // payload
  
  /*
  int sockets[2];
  char buf[4096];
  
  if (socketpair(AF_UNIX, SOCK_STREAM, 0, sockets) < 0) {
	  perror("opening stream socket pair");
	  exit(1);
  }
  
  sprintf(buf, "/home/don/scripts/create_socket.py %d:%d:%d:%d:%s:%d", sockets[0], family, type, protocol,  soup_address_get_name(SOUP_ADDRESS(connectable)),  soup_address_get_port(SOUP_ADDRESS(connectable)));

  printf(buf);

  FILE *ptr;
  ptr = popen(buf, "r");

  printf("start\n");
  int len = 0;
  int socket_fd = _recvfd(sockets[1], &len, NULL);
  printf("end\n");

  printf("socket_fd:%d\n", socket_fd);
  gsocket = g_socket_new_from_fd(socket_fd, error);
  */

  //connect(socket_fd, &addr, sizeof(struct sockaddr));

  //(void) pclose(ptr);  

  /*
  int socket_fd = socket (family, type, protocol);
  gsocket = g_socket_new_from_fd(socket_fd, error);
  connect(socket_fd, &addr, sizeof(struct sockaddr));
  */

  /*
  GValue value = { 0, { { 0 } } };
  g_object_get_property(G_OBJECT(connectable), "hostname", &value);
  */
  //printf("##connectable's hostname:%s\n", G_OBJECT_TYPE_NAME(connectable));
  //printf("##connectable's hostname:%s\n", soup_address_get_name(SOUP_ADDRESS(connectable)));
  
  /*
    gsocket = g_socket_new (family,
			 g_socket_client_get_socket_type(client),
			 g_socket_client_get_protocol(client),
			 error);

  */

  /*
  if (g_socket_client_get_local_address(client))
    {
      // this should never be executed by webkit.
#ifdef PRINT_DBG_MSG
	    fprintf(stderr, "####################### a server socket is created!");
	    exit(-1);
#endif
      if (!g_socket_bind (gsocket,
			  g_socket_client_get_local_address(client),
			  FALSE,
			  error))
	{
	  g_object_unref (gsocket);
	  return NULL;
	}
    }
  */

  if (gsocket == NULL)
    return NULL;

  if ( g_socket_client_get_timeout(client))
	  g_socket_set_timeout (gsocket,  g_socket_client_get_timeout(client));

  return gsocket;
}


/*
  DON:INFO: indirect socket creation support
*/
GSocketConnection *
g_socket_client_connect_thru_kernel (GSocketClient       *client,
				     GSocketConnectable  *connectable,
				     GCancellable        *cancellable,
				     GError             **error)
{
  GIOStream *connection = NULL;
  GSocketAddressEnumerator *enumerator = NULL;
  GError *last_error, *tmp_error;
  int trial = 0;

  last_error = NULL;
  enumerator = g_socket_connectable_enumerate (connectable);


  //#ifdef PRINT_DBG_MSG
  //fprintf(stderr, "g_socket_thru_kernel] initializing\n"); fflush(stderr);
  //#endif

  // http://developer.gnome.org/gio/2.26/GSocketConnectable.html#GSocketAddressEnumerator

  while (connection == NULL && trial < 5)
    {

      GSocketAddress *address = NULL;
      GSocket *socket;

      if (g_cancellable_is_cancelled (cancellable))
	{
	  g_clear_error (error);
	  g_cancellable_set_error_if_cancelled (cancellable, error);
	  break;
	}

      tmp_error = NULL;
      tmp_error = tmp_error;

      /* clear error from previous attempt */
      g_clear_error (&last_error);

#ifdef PRINT_DBG_MSG
      fprintf(stderr, "gsocket_thru_kernel]create_socket\n");
#endif
      // BEGIN
      // socket = create_connected_socket_thru_kernel (client, connectable, address, &last_error);
      socket = create_connected_socket_thru_kernel (client, connectable, NULL, &last_error);


      //fprintf(stderr, "gsocket_thru_kernel]created socket:t2k_soc:%d:socket:%d\n", soup_get_t2k_raw_socket(), socket);
      fflush(stderr);

      if (socket == NULL)
	{
		//g_object_unref (address);
		//continue;
		++trial;
		break;
	}

      if(soup_get_t2k_raw_socket() == 0) {
	      // DON:INFO: if the socket is created by soup itself, it's not yet connected.

	      // Don: DNS resolving is done here. We need to suppress socket
	      // connection to do that. See g_socket_address_enumerator_next()
	      // in soup-address.c

	      address = g_socket_address_enumerator_next (enumerator, cancellable,
	      					  &tmp_error);
	      if (address == NULL)
		      {
			      if (tmp_error)
				      {
					      g_clear_error (&last_error);
					      g_propagate_error (error, tmp_error);
				      }
			      else if (last_error)
				      {
					      g_propagate_error (error, last_error);
				      }
			      else
				      g_set_error_literal (error, G_IO_ERROR, G_IO_ERROR_FAILED, ("Unknown error on connect"));
			      break;
		      }

	      if (g_socket_connect (socket, address, cancellable, &last_error)) {
		      connection = (GIOStream *)g_socket_connection_factory_create_connection (socket);		   
	      } else {
		      //fprintf(stderr, "gsocket_thru_kernel]connection failed");
		      //fflush(stderr);
		      break;		      
	      }
      } else {
	      connection = (GIOStream *)g_socket_connection_factory_create_connection (socket);
      }


      /*
      socket = create_socket_thru_kernel (client, address, &last_error);
      if (socket == NULL)
	{
	  g_object_unref (address);
	  continue;
	}

      if (g_socket_connect (socket, address, cancellable, &last_error))
	connection = (GIOStream *)g_socket_connection_factory_create_connection (socket);
      */

      // END

      if (connection && g_socket_client_get_tls(client))
	{
	  GIOStream *tlsconn;

	  tlsconn = g_tls_client_connection_new (connection, connectable, &last_error);
	  g_object_unref (connection);
	  connection = tlsconn;

	  if (tlsconn)
	    {
	      g_tls_client_connection_set_validation_flags (G_TLS_CLIENT_CONNECTION (tlsconn),
                                                            g_socket_client_get_tls_validation_flags(client));
	      if (!g_tls_connection_handshake (G_TLS_CONNECTION (tlsconn),
					       cancellable, &last_error))
		{
		  g_object_unref (tlsconn);
		  connection = NULL;
		}
	    }
	}

      if (connection && !G_IS_SOCKET_CONNECTION (connection))
	{
	  GSocketConnection *wrapper_connection;

	  wrapper_connection = g_tcp_wrapper_connection_new (connection, socket);
	  g_object_unref (connection);
	  connection = (GIOStream *)wrapper_connection;
	}

      g_object_unref (socket);
      // g_object_unref (address);
    }

  g_object_unref (enumerator);

  if (connection == NULL) { 
	  //fprintf(stderr, "create_connected_socket_thru_kernel]]socket is eventuall NOT created\n"); fflush(stderr);
	  return NULL;
  }

  return G_SOCKET_CONNECTION (connection);
}

/**
 * soup_socket_connect_sync:
 * @sock: a client #SoupSocket (which must not already be connected)
 * @cancellable: a #GCancellable, or %NULL
 *
 * Attempt to synchronously connect @sock to its remote address.
 *
 * If @cancellable is non-%NULL, it can be used to cancel the
 * connection, in which case soup_socket_connect_sync() will return
 * %SOUP_STATUS_CANCELLED.
 *
 * Return value: a success or failure code.
 **/
/*
  DON:INFO: indirect socket creation support
 */
guint
soup_socket_connect_sync (SoupSocket *sock, GCancellable *cancellable)
{
	SoupSocketPrivate *priv;
	GSocketClient *client;
	GSocketConnection *conn;
	GError *error = NULL;

	g_return_val_if_fail (SOUP_IS_SOCKET (sock), SOUP_STATUS_MALFORMED);
	priv = SOUP_SOCKET_GET_PRIVATE (sock);
	g_return_val_if_fail (!priv->is_server, SOUP_STATUS_MALFORMED);
	g_return_val_if_fail (priv->gsock == NULL, SOUP_STATUS_MALFORMED);
	g_return_val_if_fail (priv->remote_addr != NULL, SOUP_STATUS_MALFORMED);

	if (cancellable)
		g_object_ref (cancellable);
	else
		cancellable = g_cancellable_new ();
	priv->connect_cancel = cancellable;

	client = g_socket_client_new ();
	if (priv->timeout)
		g_socket_client_set_timeout (client, priv->timeout);

	/*
	  DON:INFO: indirect socket creation support
	*/
	conn = g_socket_client_connect_thru_kernel (client,
						    G_SOCKET_CONNECTABLE (priv->remote_addr),
						    priv->connect_cancel, &error);
	g_object_unref (client);

	return socket_connected (sock, conn, error);
}

int
soup_socket_get_fd (SoupSocket *sock)
{
	g_return_val_if_fail (SOUP_IS_SOCKET (sock), -1);

	return g_socket_get_fd (SOUP_SOCKET_GET_PRIVATE (sock)->gsock);
}

static GSource *
soup_socket_create_watch (SoupSocketPrivate *priv, GIOCondition cond,
			  GPollableSourceFunc callback, gpointer user_data,
			  GCancellable *cancellable)
{
	GSource *watch;

	if (cond == G_IO_IN)
		watch = g_pollable_input_stream_create_source (priv->istream, cancellable);
	else
		watch = g_pollable_output_stream_create_source (priv->ostream, cancellable);
	g_source_set_callback (watch, (GSourceFunc)callback, user_data, NULL);
	g_source_attach (watch, priv->async_context);
	g_source_unref (watch);

	return watch;
}

static gboolean
listen_watch (GObject *pollable, gpointer data)
{
	SoupSocket *sock = data, *new;
	SoupSocketPrivate *priv = SOUP_SOCKET_GET_PRIVATE (sock), *new_priv;
	GSocket *new_gsock;

	new_gsock = g_socket_accept (priv->gsock, NULL, NULL);
	if (!new_gsock)
		return FALSE;

	new = g_object_new (SOUP_TYPE_SOCKET, NULL);
	new_priv = SOUP_SOCKET_GET_PRIVATE (new);
	new_priv->gsock = new_gsock;
	if (priv->async_context)
		new_priv->async_context = g_main_context_ref (priv->async_context);
	new_priv->non_blocking = priv->non_blocking;
	new_priv->is_server = TRUE;
	if (priv->ssl_creds)
		new_priv->ssl_creds = priv->ssl_creds;
	finish_socket_setup (new_priv);

	if (new_priv->ssl_creds) {
		if (!soup_socket_start_proxy_ssl (new, NULL, NULL)) {
			g_object_unref (new);
			return TRUE;
		}
	}

	g_signal_emit (sock, signals[NEW_CONNECTION], 0, new);
	g_object_unref (new);

	return TRUE;
}

/**
 * soup_socket_listen:
 * @sock: a server #SoupSocket (which must not already be connected or
 * listening)
 *
 * Makes @sock start listening on its local address. When connections
 * come in, @sock will emit %new_connection.
 *
 * Return value: whether or not @sock is now listening.
 **/
gboolean
soup_socket_listen (SoupSocket *sock)

{
	SoupSocketPrivate *priv;
	GSocketAddress *addr;

	g_return_val_if_fail (SOUP_IS_SOCKET (sock), FALSE);
	priv = SOUP_SOCKET_GET_PRIVATE (sock);
	g_return_val_if_fail (priv->gsock == NULL, FALSE);
	g_return_val_if_fail (priv->local_addr != NULL, FALSE);

	priv->is_server = TRUE;

	/* @local_addr may have its port set to 0. So we intentionally
	 * don't store it in priv->local_addr, so that if the
	 * caller calls soup_socket_get_local_address() later, we'll
	 * have to make a new addr by calling getsockname(), which
	 * will have the right port number.
	 */
	addr = soup_address_get_gsockaddr (priv->local_addr);
	g_return_val_if_fail (addr != NULL, FALSE);

	priv->gsock = g_socket_new (g_socket_address_get_family (addr),
				    G_SOCKET_TYPE_STREAM,
				    G_SOCKET_PROTOCOL_DEFAULT,
				    NULL);
	if (!priv->gsock)
		goto cant_listen;
	finish_socket_setup (priv);

	/* Bind */
	if (!g_socket_bind (priv->gsock, addr, TRUE, NULL))
		goto cant_listen;
	/* Force local_addr to be re-resolved now */
	g_object_unref (priv->local_addr);
	priv->local_addr = NULL;

	/* Listen */
	if (!g_socket_listen (priv->gsock, NULL))
		goto cant_listen;

	priv->watch_src = soup_socket_create_watch (priv, G_IO_IN,
						    listen_watch, sock,
						    NULL);
	return TRUE;

 cant_listen:
	if (priv->conn)
		disconnect_internal (sock);

	return FALSE;
}

static void
soup_socket_peer_certificate_changed (GObject *conn, GParamSpec *pspec,
				      gpointer sock)
{
	SoupSocketPrivate *priv = SOUP_SOCKET_GET_PRIVATE (sock);

	priv->tls_errors = g_tls_connection_get_peer_certificate_errors (G_TLS_CONNECTION (priv->conn));
	if (priv->ssl_ca_in_creds)
		priv->tls_errors &= ~G_TLS_CERTIFICATE_UNKNOWN_CA;

	g_object_notify (sock, "tls-certificate");
	g_object_notify (sock, "tls-errors");
}

static gboolean
soup_socket_accept_certificate (GTlsConnection *conn, GTlsCertificate *cert,
				GTlsCertificateFlags errors, gpointer sock)
{
	SoupSocketPrivate *priv = SOUP_SOCKET_GET_PRIVATE (sock);

	if (soup_ssl_credentials_verify_certificate (priv->ssl_creds,
						     cert, errors)) {
		priv->ssl_ca_in_creds = TRUE;
		return TRUE;
	}

	return !priv->ssl_strict;
}

/**
 * soup_socket_start_ssl:
 * @sock: the socket
 * @cancellable: a #GCancellable
 *
 * Starts using SSL on @socket.
 *
 * Return value: success or failure
 **/
gboolean
soup_socket_start_ssl (SoupSocket *sock, GCancellable *cancellable)
{
	SoupSocketPrivate *priv = SOUP_SOCKET_GET_PRIVATE (sock);

	return soup_socket_start_proxy_ssl (sock, soup_address_get_name (priv->remote_addr), cancellable);
}
	
/**
 * soup_socket_start_proxy_ssl:
 * @sock: the socket
 * @ssl_host: hostname of the SSL server
 * @cancellable: a #GCancellable
 *
 * Starts using SSL on @socket, expecting to find a host named
 * @ssl_host.
 *
 * Return value: success or failure
 **/
gboolean
soup_socket_start_proxy_ssl (SoupSocket *sock, const char *ssl_host,
			     GCancellable *cancellable)
{
	SoupSocketPrivate *priv = SOUP_SOCKET_GET_PRIVATE (sock);
	GTlsBackend *backend = g_tls_backend_get_default ();

	if (G_IS_TLS_CONNECTION (priv->conn))
		return TRUE;
	if (!priv->ssl_creds)
		return FALSE;

	if (!priv->is_server) {
		GTlsClientConnection *conn;
		GSocketConnectable *identity;

		identity = g_network_address_new (ssl_host, 0);
		conn = g_initable_new (g_tls_backend_get_client_connection_type (backend),
				       NULL, NULL,
				       "base-io-stream", priv->conn,
				       "server-identity", identity,
				       "use-system-certdb", FALSE,
				       "require-close-notify", FALSE,
				       "use-ssl3", TRUE,
				       NULL);
		g_object_unref (identity);

		if (!conn)
			return FALSE;

		g_object_unref (priv->conn);
		priv->conn = G_IO_STREAM (conn);

		g_signal_connect (conn, "accept-certificate",
				  G_CALLBACK (soup_socket_accept_certificate),
				  sock);
	} else {
		GTlsServerConnection *conn;

		conn = g_initable_new (g_tls_backend_get_server_connection_type (backend),
				       NULL, NULL,
				       "base-io-stream", priv->conn,
				       "certificate", soup_ssl_credentials_get_certificate (priv->ssl_creds),
				       "use-system-certdb", FALSE,
				       "require-close-notify", FALSE,
				       NULL);
		if (!conn)
			return FALSE;

		g_object_unref (priv->conn);
		priv->conn = G_IO_STREAM (conn);
	}

	priv->ssl_ca_in_creds = FALSE;
	g_signal_connect (priv->conn, "notify::peer-certificate",
			  G_CALLBACK (soup_socket_peer_certificate_changed), sock);

	priv->istream = G_POLLABLE_INPUT_STREAM (g_io_stream_get_input_stream (priv->conn));
	priv->ostream = G_POLLABLE_OUTPUT_STREAM (g_io_stream_get_output_stream (priv->conn));
	return TRUE;
}
	
/**
 * soup_socket_is_ssl:
 * @sock: a #SoupSocket
 *
 * Tests if @sock is set up to do SSL. Note that this simply means
 * that the %SOUP_SOCKET_SSL_CREDENTIALS property has been set; it
 * does not mean that soup_socket_start_ssl() has been called.
 *
 * Return value: %TRUE if @sock has SSL credentials set
 **/
gboolean
soup_socket_is_ssl (SoupSocket *sock)
{
	SoupSocketPrivate *priv = SOUP_SOCKET_GET_PRIVATE (sock);

	return priv->ssl_creds != NULL;
}

/**
 * soup_socket_disconnect:
 * @sock: a #SoupSocket
 *
 * Disconnects @sock. Any further read or write attempts on it will
 * fail.
 **/
void
soup_socket_disconnect (SoupSocket *sock)
{
	SoupSocketPrivate *priv;
	gboolean already_disconnected = FALSE;

	g_return_if_fail (SOUP_IS_SOCKET (sock));
	priv = SOUP_SOCKET_GET_PRIVATE (sock);

	if (priv->connect_cancel) {
		g_cancellable_cancel (priv->connect_cancel);
		return;
	} else if (g_mutex_trylock (priv->iolock)) {
		if (priv->conn)
			disconnect_internal (sock);
		else
			already_disconnected = TRUE;
		g_mutex_unlock (priv->iolock);
	} else {
		/* Another thread is currently doing IO, so
		 * we can't close the socket. So just shutdown
		 * the file descriptor to force the I/O to fail.
		 * (It will actually be closed when the socket
		 * is destroyed.)
		 */
		g_socket_shutdown (priv->gsock, TRUE, TRUE, NULL);
	}

	if (already_disconnected)
		return;

	/* Keep ref around signals in case the object is unreferenced
	 * in a handler
	 */
	g_object_ref (sock);

	/* Give all readers a chance to notice the connection close */
	g_signal_emit (sock, signals[READABLE], 0);

	/* FIXME: can't disconnect until all data is read */

	/* Then let everyone know we're disconnected */
	g_signal_emit (sock, signals[DISCONNECTED], 0);

	g_object_unref (sock);
}

/**
 * soup_socket_is_connected:
 * @sock: a #SoupSocket
 *
 * Tests if @sock is connected to another host
 *
 * Return value: %TRUE or %FALSE.
 **/
gboolean
soup_socket_is_connected (SoupSocket *sock)
{
	SoupSocketPrivate *priv;

	g_return_val_if_fail (SOUP_IS_SOCKET (sock), FALSE);
	priv = SOUP_SOCKET_GET_PRIVATE (sock);

	return priv->conn != NULL;
}

/**
 * soup_socket_get_local_address:
 * @sock: a #SoupSocket
 *
 * Returns the #SoupAddress corresponding to the local end of @sock.
 *
 * Return value: (transfer none): the #SoupAddress
 **/
SoupAddress *
soup_socket_get_local_address (SoupSocket *sock)
{
	SoupSocketPrivate *priv;

	g_return_val_if_fail (SOUP_IS_SOCKET (sock), NULL);
	priv = SOUP_SOCKET_GET_PRIVATE (sock);

	g_mutex_lock (priv->addrlock);
	if (!priv->local_addr) {
		GSocketAddress *addr;
		struct sockaddr_storage sa;
		gssize sa_len;

		addr = g_socket_get_local_address (priv->gsock, NULL);
		sa_len = g_socket_address_get_native_size (addr);
		g_socket_address_to_native (addr, &sa, sa_len, NULL);
		priv->local_addr = soup_address_new_from_sockaddr ((struct sockaddr *)&sa, sa_len);
		g_object_unref (addr);
	}
	g_mutex_unlock (priv->addrlock);

	return priv->local_addr;
}

/**
 * soup_socket_get_remote_address:
 * @sock: a #SoupSocket
 *
 * Returns the #SoupAddress corresponding to the remote end of @sock.
 *
 * Return value: (transfer none): the #SoupAddress
 **/
SoupAddress *
soup_socket_get_remote_address (SoupSocket *sock)
{
	SoupSocketPrivate *priv;

	g_return_val_if_fail (SOUP_IS_SOCKET (sock), NULL);
	priv = SOUP_SOCKET_GET_PRIVATE (sock);

	g_mutex_lock (priv->addrlock);
	if (!priv->remote_addr) {
		GSocketAddress *addr;
		struct sockaddr_storage sa;
		gssize sa_len;

		addr = g_socket_get_remote_address (priv->gsock, NULL);
		sa_len = g_socket_address_get_native_size (addr);
		g_socket_address_to_native (addr, &sa, sa_len, NULL);
		priv->remote_addr = soup_address_new_from_sockaddr ((struct sockaddr *)&sa, sa_len);
		g_object_unref (addr);
	}
	g_mutex_unlock (priv->addrlock);

	return priv->remote_addr;
}


static gboolean
socket_read_watch (GObject *pollable, gpointer user_data)
{
	SoupSocket *sock = user_data;
	SoupSocketPrivate *priv = SOUP_SOCKET_GET_PRIVATE (sock);

	priv->read_src = NULL;
	g_signal_emit (sock, signals[READABLE], 0);
	return FALSE;
}

static SoupSocketIOStatus
read_from_network (SoupSocket *sock, gpointer buffer, gsize len,
		   gsize *nread, GCancellable *cancellable, GError **error)
{
	SoupSocketPrivate *priv = SOUP_SOCKET_GET_PRIVATE (sock);
	GError *my_err = NULL;
	gssize my_nread;

	*nread = 0;

	if (!priv->conn)
		return SOUP_SOCKET_EOF;

	if (!priv->non_blocking) {
		my_nread = g_input_stream_read (G_INPUT_STREAM (priv->istream),
						buffer, len,
						cancellable, &my_err);
	} else {
		my_nread = g_pollable_input_stream_read_nonblocking (
			priv->istream, buffer, len,
			cancellable, &my_err);
	}

	if (my_nread > 0) {
		g_clear_error (&my_err);
		*nread = my_nread;
		return SOUP_SOCKET_OK;
	} else if (my_nread == 0) {
		g_clear_error (&my_err);
		*nread = my_nread;
		return SOUP_SOCKET_EOF;
	} else if (g_error_matches (my_err, G_IO_ERROR, G_IO_ERROR_WOULD_BLOCK)) {
		g_clear_error (&my_err);
		if (!priv->read_src) {
			priv->read_src =
				soup_socket_create_watch (priv, G_IO_IN,
							  socket_read_watch, sock,
							  cancellable);
		}
		return SOUP_SOCKET_WOULD_BLOCK;
	} else if (g_error_matches (my_err, G_TLS_ERROR, G_TLS_ERROR_HANDSHAKE)) {
		my_err->domain = SOUP_SSL_ERROR;
		my_err->code = SOUP_SSL_ERROR_CERTIFICATE;
	}

	g_propagate_error (error, my_err);
	return SOUP_SOCKET_ERROR;
}

static SoupSocketIOStatus
read_from_buf (SoupSocket *sock, gpointer buffer, gsize len, gsize *nread)
{
	SoupSocketPrivate *priv = SOUP_SOCKET_GET_PRIVATE (sock);
	GByteArray *read_buf = priv->read_buf;

	*nread = MIN (read_buf->len, len);
	memcpy (buffer, read_buf->data, *nread);

	if (*nread == read_buf->len) {
		g_byte_array_free (read_buf, TRUE);
		priv->read_buf = NULL;
	} else {
		memmove (read_buf->data, read_buf->data + *nread, 
			 read_buf->len - *nread);
		g_byte_array_set_size (read_buf, read_buf->len - *nread);
	}

	return SOUP_SOCKET_OK;
}

/**
 * SoupSocketIOStatus:
 * @SOUP_SOCKET_OK: Success
 * @SOUP_SOCKET_WOULD_BLOCK: Cannot read/write any more at this time
 * @SOUP_SOCKET_EOF: End of file
 * @SOUP_SOCKET_ERROR: Other error
 *
 * Return value from the #SoupSocket IO methods.
 **/

/**
 * soup_socket_read:
 * @sock: the socket
 * @buffer: buffer to read into
 * @len: size of @buffer in bytes
 * @nread: on return, the number of bytes read into @buffer
 * @cancellable: a #GCancellable, or %NULL
 * @error: error pointer
 *
 * Attempts to read up to @len bytes from @sock into @buffer. If some
 * data is successfully read, soup_socket_read() will return
 * %SOUP_SOCKET_OK, and *@nread will contain the number of bytes
 * actually read (which may be less than @len).
 *
 * If @sock is non-blocking, and no data is available, the return
 * value will be %SOUP_SOCKET_WOULD_BLOCK. In this case, the caller
 * can connect to the #SoupSocket::readable signal to know when there
 * is more data to read. (NB: You MUST read all available data off the
 * socket first. #SoupSocket::readable is only emitted after
 * soup_socket_read() returns %SOUP_SOCKET_WOULD_BLOCK, and it is only
 * emitted once. See the documentation for #SoupSocket:non-blocking.)
 *
 * Return value: a #SoupSocketIOStatus, as described above (or
 * %SOUP_SOCKET_EOF if the socket is no longer connected, or
 * %SOUP_SOCKET_ERROR on any other error, in which case @error will
 * also be set).
 **/
SoupSocketIOStatus
soup_socket_read (SoupSocket *sock, gpointer buffer, gsize len,
		  gsize *nread, GCancellable *cancellable, GError **error)
{
	SoupSocketPrivate *priv;
	SoupSocketIOStatus status;

	g_return_val_if_fail (SOUP_IS_SOCKET (sock), SOUP_SOCKET_ERROR);
	g_return_val_if_fail (nread != NULL, SOUP_SOCKET_ERROR);

	priv = SOUP_SOCKET_GET_PRIVATE (sock);

	g_mutex_lock (priv->iolock);
	if (priv->read_buf)
		status = read_from_buf (sock, buffer, len, nread);
	else
		status = read_from_network (sock, buffer, len, nread, cancellable, error);
	g_mutex_unlock (priv->iolock);

	return status;
}

/**
 * soup_socket_read_until:
 * @sock: the socket
 * @buffer: buffer to read into
 * @len: size of @buffer in bytes
 * @boundary: boundary to read until
 * @boundary_len: length of @boundary in bytes
 * @nread: on return, the number of bytes read into @buffer
 * @got_boundary: on return, whether or not the data in @buffer
 * ends with the boundary string
 * @cancellable: a #GCancellable, or %NULL
 * @error: error pointer
 *
 * Like soup_socket_read(), but reads no further than the first
 * occurrence of @boundary. (If the boundary is found, it will be
 * included in the returned data, and *@got_boundary will be set to
 * %TRUE.) Any data after the boundary will returned in future reads.
 *
 * soup_socket_read_until() will almost always return fewer than @len
 * bytes: if the boundary is found, then it will only return the bytes
 * up until the end of the boundary, and if the boundary is not found,
 * then it will leave the last <literal>(boundary_len - 1)</literal>
 * bytes in its internal buffer, in case they form the start of the
 * boundary string. Thus, @len normally needs to be at least 1 byte
 * longer than @boundary_len if you want to make any progress at all.
 *
 * Return value: as for soup_socket_read()
 **/
SoupSocketIOStatus
soup_socket_read_until (SoupSocket *sock, gpointer buffer, gsize len,
			gconstpointer boundary, gsize boundary_len,
			gsize *nread, gboolean *got_boundary,
			GCancellable *cancellable, GError **error)
{
	SoupSocketPrivate *priv;
	SoupSocketIOStatus status;
	GByteArray *read_buf;
	guint match_len, prev_len;
	guint8 *p, *end;

	g_return_val_if_fail (SOUP_IS_SOCKET (sock), SOUP_SOCKET_ERROR);
	g_return_val_if_fail (nread != NULL, SOUP_SOCKET_ERROR);
	g_return_val_if_fail (len >= boundary_len, SOUP_SOCKET_ERROR);

	priv = SOUP_SOCKET_GET_PRIVATE (sock);

	g_mutex_lock (priv->iolock);

	*got_boundary = FALSE;

	if (!priv->read_buf)
		priv->read_buf = g_byte_array_new ();
	read_buf = priv->read_buf;

	if (read_buf->len < boundary_len) {
		prev_len = read_buf->len;
		g_byte_array_set_size (read_buf, len);
		status = read_from_network (sock,
					    read_buf->data + prev_len,
					    len - prev_len, nread, cancellable, error);
		read_buf->len = prev_len + *nread;

		if (status != SOUP_SOCKET_OK) {
			g_mutex_unlock (priv->iolock);
			return status;
		}
	}

	/* Scan for the boundary */
	end = read_buf->data + read_buf->len;
	for (p = read_buf->data; p <= end - boundary_len; p++) {
		if (!memcmp (p, boundary, boundary_len)) {
			p += boundary_len;
			*got_boundary = TRUE;
			break;
		}
	}

	/* Return everything up to 'p' (which is either just after the
	 * boundary, or @boundary_len - 1 bytes before the end of the
	 * buffer).
	 */
	match_len = p - read_buf->data;
	status = read_from_buf (sock, buffer, MIN (len, match_len), nread);

	g_mutex_unlock (priv->iolock);
	return status;
}

static gboolean
socket_write_watch (GObject *pollable, gpointer user_data)
{
	SoupSocket *sock = user_data;
	SoupSocketPrivate *priv = SOUP_SOCKET_GET_PRIVATE (sock);

	priv->write_src = NULL;
	g_signal_emit (sock, signals[WRITABLE], 0);
	return FALSE;
}

/**
 * soup_socket_write:
 * @sock: the socket
 * @buffer: data to write
 * @len: size of @buffer, in bytes
 * @nwrote: on return, number of bytes written
 * @cancellable: a #GCancellable, or %NULL
 * @error: error pointer
 *
 * Attempts to write @len bytes from @buffer to @sock. If some data is
 * successfully written, the return status will be %SOUP_SOCKET_OK,
 * and *@nwrote will contain the number of bytes actually written
 * (which may be less than @len).
 *
 * If @sock is non-blocking, and no data could be written right away,
 * the return value will be %SOUP_SOCKET_WOULD_BLOCK. In this case,
 * the caller can connect to the #SoupSocket::writable signal to know
 * when more data can be written. (NB: #SoupSocket::writable is only
 * emitted after soup_socket_write() returns %SOUP_SOCKET_WOULD_BLOCK,
 * and it is only emitted once. See the documentation for
 * #SoupSocket:non-blocking.)
 *
 * Return value: a #SoupSocketIOStatus, as described above (or
 * %SOUP_SOCKET_EOF or %SOUP_SOCKET_ERROR. @error will be set if the
 * return value is %SOUP_SOCKET_ERROR.)
 **/
SoupSocketIOStatus
soup_socket_write (SoupSocket *sock, gconstpointer buffer,
		   gsize len, gsize *nwrote,
		   GCancellable *cancellable, GError **error)
{
	SoupSocketPrivate *priv;
	GError *my_err = NULL;
	gssize my_nwrote;

	g_return_val_if_fail (SOUP_IS_SOCKET (sock), SOUP_SOCKET_ERROR);
	g_return_val_if_fail (nwrote != NULL, SOUP_SOCKET_ERROR);

	priv = SOUP_SOCKET_GET_PRIVATE (sock);

	g_mutex_lock (priv->iolock);

	if (!priv->conn) {
		g_mutex_unlock (priv->iolock);
		return SOUP_SOCKET_EOF;
	}
	if (priv->write_src) {
		g_mutex_unlock (priv->iolock);
		return SOUP_SOCKET_WOULD_BLOCK;
	}

	if (!priv->non_blocking) {
		my_nwrote = g_output_stream_write (G_OUTPUT_STREAM (priv->ostream),
						   buffer, len,
						   cancellable, &my_err);
	} else {
		my_nwrote = g_pollable_output_stream_write_nonblocking (
			priv->ostream, buffer, len,
			cancellable, &my_err);
	}

	if (my_nwrote > 0) {
		g_mutex_unlock (priv->iolock);
		g_clear_error (&my_err);
		*nwrote = my_nwrote;
		return SOUP_SOCKET_OK;
	}

	if (g_error_matches (my_err, G_IO_ERROR, G_IO_ERROR_WOULD_BLOCK)) {
		g_mutex_unlock (priv->iolock);

		priv->write_src =
			soup_socket_create_watch (priv,
						  G_IO_OUT,
						  socket_write_watch, sock, cancellable);
		return SOUP_SOCKET_WOULD_BLOCK;
	} else if (g_error_matches (my_err, G_TLS_ERROR, G_TLS_ERROR_HANDSHAKE)) {
		my_err->domain = SOUP_SSL_ERROR;
		my_err->code = SOUP_SSL_ERROR_CERTIFICATE;
	}

	g_mutex_unlock (priv->iolock);
	g_propagate_error (error, my_err);
	return SOUP_SOCKET_ERROR;
}
