#!/usr/bin/env python

import subprocess
import passfd
import socket
import string
import struct

FAMILY = socket.AF_UNIX
TYPE   = socket.SOCK_STREAM

sP, sC = socket.socketpair(FAMILY, TYPE)
#subprocess.Popen(["/usr/bin/strace",  "./hybrid_browser2.py", str(sC.fileno())])
#subprocess.Popen(["./hybrid_browser.py", str(sC.fileno())])
subprocess.Popen(["./browser.py", str(sC.fileno())])
#subprocess.Popen(["./hybrid_browser2.py", str(sC.fileno())])

tab_waiting = False

while True : 
  try :
    # RequestSocket 
    tag = sP.recv(13)
    print "K]]received tag:[" + tag + "]"
    tab_waiting = True
    # skip the null character
    sP.recv(1)
    # recieve all the msg including the null character
    msg = sP.recv(512)
    msg = msg[0:len(msg) - 1]
    print "K]]received msg:[" + msg + "]"
    flds = string.split(msg, ":")
    hostname = flds[0]
    port = int(flds[1])
    family = int(flds[2])
    stype = int(flds[3])
    protocol = int(flds[4])

    print "K]]a socket is created in the kernel"
    print "K]]hostname:" + str(hostname)
    print "K]]port:" + str(port)
    print "K]]family:" + str(family)
    print "K]]stype:" + str(stype)
    print "K]]protocol:" + str(protocol)

    s = socket.socket(family, stype)
    s.connect((hostname, port))

    sP.send("ResultSocket\0")
    passfd.sendfd(sP, s.fileno(), message="\x00")
    tab_waiting = False
  except:
    print "KERNEL]socket creation failed"
    if tab_waiting :
      sP.send("ResultSocket\0")
      passfd.sendfd(sP, 0 , message="\x00")


    
