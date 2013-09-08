#!/bin/bash

procids=`ps -aux | grep 'python ./kernel.py' | awk '{FS=" ";print $2}'`
for pid in $procids
do
	kill -9 $pid
done

procids=`ps -aux | grep 'python ./hybrid_browser.py' | awk '{FS=" ";print $2}'`
for pid in $procids
do
	kill -9 $pid
done


./kernel.py
