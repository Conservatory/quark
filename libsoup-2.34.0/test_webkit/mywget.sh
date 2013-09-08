#!/bin/bash

USER_AGENT="Mozilla/5.0 (X11; Linux i686) AppleWebKit/534.30 (KHTML, like Gecko) Ubuntu/11.04 Chromium/12.0.742.112 Chrome/12.0.742.112 Safari/534.30"

echo "=============================================" >> wget.out
echo "ORIGIN:$1" >> wget.out

/usr/bin/wget --tries=1 --timeout=2 --server-response --convert-links -a wget.out -O webfile -U "$USER_AGENT" $2 2>>wget.err

