#!/usr/bin/env python

import subprocess
import passfd
import socket
import string
import struct
import fcntl
import sys
import os

FAMILY = socket.AF_UNIX
TYPE   = socket.SOCK_STREAM

sP, sC = socket.socketpair(FAMILY, TYPE)
sP.setblocking(0)
# sC remains as blocking mode

#subprocess.Popen(["/usr/bin/strace",  "./browser.py", str(sC.fileno())])


subprocess.Popen(["./browser.py", str(sC.fileno())])

socket_list = []
tab_waiting_for_socket = False

while True : 
  #print "K]] event loop"

  # data transfer
  for socks in socket_list:
    #print "socket is found"
    # T->K->I
    try :
      data = socks[1].recv(4096)
      if len(data) > 0:
        socks[0].send(data)

      try :
        socks[0].sendall()
      except:
        pass

    except :
      pass
    
      #print "K]] data transfer(T->K->I) failed"

    # I->K->T
    try :
      data = socks[0].recv(4096)
      #if len(data) > 0 and string.find(data, "Content-Type:") != -1:
      # print >> sys.stderr, data
      if len(data) > 0:
        socks[1].send(data)

      try :
        socks[1].sendall()
      except:
        pass

    except :
      pass
      #print "K]] data transfer(I->K->T) failed"

  # socket creation 
  try :
    family = struct.unpack("i", sP.recv(4))[0]
    tab_waiting_for_socket = True

    stype = struct.unpack("i", sP.recv(4))[0]
    protocol = struct.unpack("i", sP.recv(4))[0]
    port = struct.unpack("i", sP.recv(4))[0]
    hostname = sP.recv(4096)

    print "K]]a socket is created in the kernel"
    print "K]]family:" + str(family)
    print "K]]stype:" + str(stype)
    print "K]]protocol:" + str(protocol)
    print "K]]port:" + str(port)
    print "K]]hostname:" + str(hostname)

    # a real socket is created 
    real_s = socket.socket(family, stype)
    real_s.connect((hostname, port))
    real_s.setblocking(0)

    # creates sockets that the kernel & the tab are communicating with each other
    ssP, ssC = socket.socketpair(socket.AF_UNIX, socket.SOCK_STREAM)
    ssP.setblocking(0)
    ssC.setblocking(0)

    # ssC remains as blocked

    socket_list.append([real_s,ssP])
    passfd.sendfd(sP, ssC.fileno(), message="\x00")

    tab_waiting_for_socket = False
  except:
    #print "KERNEL]socket creation failed"
    if tab_waiting_for_socket :
        passfd.sendfd(sP, 0 , message="\x00")

