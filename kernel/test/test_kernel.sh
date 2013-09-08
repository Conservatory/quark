#!/bin/bash
stty cbreak
# this line causes a very strange problem.
# it works well. but the process is automatically killed by an unknown reason.
# echo "+" | ./main.native 2>./stderr.txt
#echo "Press F11 to create a tab / F12 to do mouse click"
cd ..
export LD_LIBRARY_PATH=.:/usr/local/lib
../../../python-browser-8/input_gen.py $1 | ./main.native 2>>./test/test_stderr.txt

