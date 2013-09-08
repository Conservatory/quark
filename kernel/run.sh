#!/bin/bash

#export PATH=$PATH:../../../python-browser-8
xhost + >/dev/null
killall run_kernel.sh 2>/dev/null
rm tabno.tmp 2>/dev/null
xterm -title "Quark Web Browser Kernel" -geometry 110x5+100+155 -fn *-fixed-*-*-*-20-* -e ./run_kernel.sh &
#tail -f stderr.txt
