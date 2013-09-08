#!/bin/bash
export PATH=$PATH:../../../python-browser-8
#export DISPLAY=:0.0
#declare -x DISPLAY="localhost:0.0"

if [ -z `which getcurpos` ]
then
	echo "cannot find getcurpos in the execution path"
	echo "it should be located in ../../../python-browser-4"
	echo "compiling..."

	cd ../../../python-browser-4
	gcc -o getcurpos getcurpos.c -lX11
	cd ../ynot/examples/vcr
fi

#if [ -z `which xdotool` ]
#then
#	echo "cannot find xdotool in the execution path"
#	echo "install : sudo apt-get install xdotool"
#	sudo apt-get install xdotool
#fi

#if [ -z `which xwininfo` ]
#then
#	echo "cannot find xwininfo in the execution path"
#	echo "install : sudo apt-get install xwininfo"
#	sudo apt-get install xwininfo
#fi

#killall xdotool

rm test_stderr.txt
touch test_stderr.txt

WEBSITES="google.com
facebook.com
youtube.com
yahoo.com
amazon.com
wikipedia.org
twitter.com
ebay.com
accounts.google.com
craigslist.org"

#WEBSITES="youtube.com
#amazon.com"

#WEBSITES="amazon.com"

#accounts.google.com = www.blogger.com
#WEBSITES="youtube.com
#yahoo.com
#amazon.com"
#WEBSITES="yahoo.com"

#WEBSITES="google.com"

killall xterm 
killall python 
killall test_kernel.sh 

for i in $WEBSITES; do
    for j in {1..5}
    do
	cp test_stderr.txt test_stderr.txt.tmp
	xterm -title "Quark Web Browser Kernel" -geometry 110x5+100+40 -fn *-fixed-*-*-*-20-* -e ./test_kernel.sh $i &

	for k in {1..40}
	do
	    command="diff test_stderr.txt test_stderr.txt.tmp | grep 'PAGING LOADING TIME:0:$i'"
	    check_result=`eval $command`
	    if [[ -z $check_result ]]; 
	    then
		# not finished
		sleep 1
		continue
	    else
		# finished
		break
	    fi
	done

	killall -s SIGINT python 2>/dev/null
	sleep 1
	killall test_kernel.sh 2>/dev/null
	sleep 1
	killall xterm 2>/dev/null
	# wait till the mess is cleared up
    done
done

#sleep 1
#sleep 1

#wmctrl -r "Quark Web Browser Kernel" -e 0,20,20,1100,125
#wmctrl -r "Quark Web Browser Output" -e 0,27,178,1100,500

#OUTPUTWIN_ID=`xdotool search -name "Quark Web Browser Output"`
#KERNEL_ID=`xdotool search -name "Quark Web Browser Kernel"`

#xdotool behave $OUTPUTWIN_ID focus windowraise $KERNEL_ID &
#echo "xdotool behave $OUTPUTWIN_ID mouse-enter windowraise $KERNEL_ID"

#xdotool behave $OUTPUTWIN_ID mouse-enter windowraise $KERNEL_ID &
#xdotool behave $OUTPUTWIN_ID mouse-enter windowfocus $KERNEL_ID &
#xdotool behave $KERNEL_ID focus windowraise $OUTPUTWIN_ID &

