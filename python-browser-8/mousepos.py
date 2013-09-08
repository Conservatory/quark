#!/usr/bin/env python

# Quark is Copyright (C) 2012-2015, Quark Team.
#
# You can redistribute and modify it under the terms of the GNU GPL,
# version 2 or later, but it is made available WITHOUT ANY WARRANTY.
#
# For more information about Quark, see our web site at:
# http://goto.ucsd.edu/quark/


import sys
import os
import re
import subprocess
import msg
import cPickle as pickle

line = os.popen("xwininfo -name 'Quark Web Browser Output'").read()
m = re.search("Absolute upper-left X:(\s+)(\S+)(\s+)Absolute upper-left Y:(\s+)(\S+)", line)
outputx = int(m.group(2))
outputy = int(m.group(5))

line = os.popen("~/vcr/python-browser-8/getcurpos").read()
#m = re.search(r"x:(\d+) y:(\d+) screen:(\d+)", line)
m = re.search(r"(\d+) (\d+)", line)
mousex = int(m.group(1)) - outputx
mousey = int(m.group(2)) - outputy

if mousex < 0:
    mousex = 0

if mousey < 0:
    mousey = 0

pickle.dump((mousex, mousey), sys.stdout)



