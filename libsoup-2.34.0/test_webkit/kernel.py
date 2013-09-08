#!/usr/bin/env python

import subprocess
import passfd
import socket
import string
import struct

FAMILY = socket.AF_UNIX
TYPE   = socket.SOCK_STREAM

sP, sC = socket.socketpair(FAMILY, TYPE)
subprocess.Popen(["/usr/bin/strace",  "./hybrid_browser2.py", str(sC.fileno())])
#subprocess.Popen(["./hybrid_browser.py", str(sC.fileno())])
#subprocess.Popen(["./browser.py", str(sC.fileno())])
#subprocess.Popen(["./hybrid_browser2.py", str(sC.fileno())])


tab_waiting = False

while True : 
  try :
    family = struct.unpack("i", sP.recv(4))[0]
    tab_waiting = True

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

    s = socket.socket(family, stype)
    s.connect((hostname, port))
    passfd.sendfd(sP, s.fileno(), message="\x00")
    tab_waiting = False
  except:
    #raise
    print "KERNEL]socket creation failed"
    if tab_waiting :
        passfd.sendfd(sP, 0 , message="\x00")


    
