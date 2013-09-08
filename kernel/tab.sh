#!/bin/bash

#chroot /var/chroot unshare -n "~/vcr/python-browser-8/tab.py" "$1" "$2" "$3" 
#strace "~/vcr/python-browser-8/tab.py" "$1" "$2" "$3" 
#strace -f -F ~/vcr/python-browser-8/tab.py "$1" "$2" "$3"
#~/vcr/python-browser-8/tab.py $1 $2 $3
#ulimit -c unlimited

tabno=0
if [ -f "tabno.tmp" ]
then
    tabno=`cat tabno.tmp`
    tabno=$(($tabno+1))
else
    echo 0 > tabno.tmp
fi

#~/vcr/python-browser-8/tab$tabno.py $1 $2 $3
#echo "~/vcr/python-browser-8/tab_exec $tabno $1 $2 $3"
suid=`id -u tab$tabno`
~/vcr/python-browser-8/tab_exec $suid $1 $2 $3 
#~/vcr/python-browser-8/tab.py $1 $2 $3 
