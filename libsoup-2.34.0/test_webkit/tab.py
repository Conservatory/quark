#!/usr/bin/env python

import subprocess
import passfd
import sys
import socket

FAMILY = socket.AF_UNIX
TYPE   = socket.SOCK_STREAM

tab2kernel = socket.fromfd(int(sys.argv[1]), FAMILY, TYPE)

#tab2kernel.send("firebird.ucsd.edu:80")
#print tab2kernel.recv(4096)

while True:
  try : 
    data = sys.stdin.readline()
    tab2kernel.send(data)
    (fd, msg) = passfd.recvfd(tab2kernel, msg_buf=4096)

    print msg


    if int(fd) == 0:
        print "tab:connection failed"
    else:
        http_soc = socket.fromfd(int(fd), FAMILY, TYPE)
        http_soc.send("GET /index.html\n")
        print http_soc.recv(4096)
        http_soc.close()
  except:
    print "tab:error"

