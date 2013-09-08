/* vim:ts=4:sw=4:et:ai:sts=4
 *
 * passfd.c: Functions to pass file descriptors across UNIX domain sockets.
 *
 * Please note that this only supports BSD-4.3+ style file descriptor passing,
 * and was only tested on Linux. Patches are welcomed!
 *
 * Copyright © 2010 Martín Ferrari <martin.ferrari@gmail.com>
 *
 * Inspired by Socket::PassAccessRights, which is:
 *   Copyright (c) 2000 Sampo Kellomaki <sampo@iki.fi>
 *
 * For more information, see one of the R. Stevens' books:
 * - Richard Stevens: Unix Network Programming, Prentice Hall, 1990;
 *   chapter 6.10
 * 
 * - Richard Stevens: Advanced Programming in the UNIX Environment,
 *   Addison-Wesley, 1993; chapter 15.3
 *
 * This program is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License as published by the Free
 * Software Foundation; either version 2 of the License, or (at your option)
 * any later version.
 *
 * This program is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
 * more details.
 *
 * You should have received a copy of the GNU General Public License along with
 * this program; if not, write to the Free Software Foundation, Inc., 51
 * Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA.
 */

#include <sys/types.h>
#include <sys/socket.h>
#include <unistd.h>
#include <caml/mlvalues.h>

#include <stdio.h>

/* Size of the cmsg including one file descriptor */
#define CMSG_SIZE CMSG_SPACE(sizeof(int))

/* 
 * _sendfd(): send a message and piggyback a file descriptor.
 *
 * Note that the file descriptor cannot be sent by itself, at least one byte of
 * payload needs to be sent.
 *
 * Parameters:
 *  sock: AF_UNIX socket
 *  fd:   file descriptor to pass
 *  len:  length of the message
 *  msg:  the message itself
 *
 * Return value:
 *  On success, sendfd returns the number of characters from the message sent,
 *  the file descriptor information is not taken into account. If there was no
 *  message to send, 0 is returned. On error, -1 is returned, and errno is set
 *  appropriately.
 *
 */
CAMLprim value _sendfd(value v0, value v1) {

    //return ret;
    //fprintf(stderr, "start] _sendfd \n");
    // fflush(stderr);

    int sock = Int_val(v0);
    int fd = Int_val(v1);

    struct iovec iov[1];
    struct msghdr msgh;
    char buf[CMSG_SIZE];
    struct cmsghdr *h;
    int ret;

    int len = 1;
    char* msg = "\0";

    /* At least one byte needs to be sent, for some reason (?) */
    if(len < 1) {
        //fprintf(stderr, "error] _sendfd \n");
        //fflush(stderr);
        return Val_unit;
    }

    memset(&iov[0], 0, sizeof(struct iovec));
    memset(&msgh, 0, sizeof(struct msghdr));
    memset(buf, 0, CMSG_SIZE);

    msgh.msg_name       = NULL;
    msgh.msg_namelen    = 0;

    msgh.msg_iov        = iov;
    msgh.msg_iovlen     = 1;

    msgh.msg_control    = buf;
    msgh.msg_controllen = CMSG_SIZE;
    msgh.msg_flags      = 0;

    /* Message to be sent */
    iov[0].iov_base = (void *)msg;
    iov[0].iov_len  = len;

    /* Control data */
    h = CMSG_FIRSTHDR(&msgh);
    h->cmsg_len   = CMSG_LEN(sizeof(int));
    h->cmsg_level = SOL_SOCKET;
    h->cmsg_type  = SCM_RIGHTS;
    ((int *)CMSG_DATA(h))[0] = fd;

    /*
    fprintf(stderr, "kernel-sendmsg] is called\n");
    fflush(stderr);
    */

    ret = sendmsg(sock, &msgh, 0);

    /*
    fprintf(stderr, "kernel-sendmsg] is finished\n");
    fflush(stderr);
    */
    //return ret;
    //fprintf(stderr, "end] _sendfd is successfully finished:sock:%d,fd:%d,ret:%d\n",sock,fd,ret);
    //fflush(stderr);

    return Val_unit;
}


/* 
 * _recvfd(): receive a message and a file descriptor.
 *
 * Parameters:
 *  sock: AF_UNIX socket
 *  len:  pointer to the length of the message buffer, modified on return
 *  buf:  buffer to contain the received buffer
 *
 * If len is 0 or buf is NULL, the received message is stored in a temporary
 * buffer and discarded later.
 *
 * Return value:
 *  On success, recvfd returns the received file descriptor, and len points to
 *  the size of the received message. 
 *  If recvmsg fails, -1 is returned, and errno is set appropriately.
 *  If the received data does not carry exactly one file descriptor, -2 is
 *  returned. If the received file descriptor is not valid, -3 is returned.
 *
 */
int _recvfd(int sock, size_t *len, void *buf) {
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
        
    st = recvmsg(sock, &msgh, 0);
    if(st < 0)
        return -1;

    *len = st;
    h = CMSG_FIRSTHDR(&msgh);
    /* Check if we received what we expected */
    if(h == NULL
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


CAMLprim value _int_of_file_descr(value v0) {
  return Val_int(Int_val(v0));
}

CAMLprim value _file_descr_of_int(value v0) {
  return v0;
}

/*
CAMLprim value _int_of_file_descr(value v0) {
  return Val_int(Int_val(v0));
}
*/
