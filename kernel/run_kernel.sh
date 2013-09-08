#!/bin/bash
stty cbreak
# this line causes a very strange problem.
# it works well. but the process is automatically killed by an unknown reason.
# echo "+" | ./main.native 2>./stderr.txt
#echo "Press F11 to create a tab / F12 to do mouse click"
export LD_LIBRARY_PATH=.:/usr/local/lib:/usr/lib/i386-linux-gnu/
touch stderr.txt 2>/dev/null
chmod 777 stderr.txt 2>/dev/null
../python-browser-8/input.py | ./main.native 2>./stderr.txt
