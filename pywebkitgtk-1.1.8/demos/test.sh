#!/bin/bash

rm rtest_stderr.txt

WEBSITES="google.com
facebook.com
youtube.com
yahoo.com
amazon.com
wikipedia.org
twitter.com
ebay.com
blogger.com
craigslist.org"

#WEBSITES="youtube.com
#amazon.com"

for i in $WEBSITES; do
    for j in {1..10}
    do
	./browser.py http://$i  &
	sleep 10
	killall python 2>/dev/null
    done
done

