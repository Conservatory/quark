#!/bin/bash
export PATH=$PATH:../../../python-browser-8
#export DISPLAY=:0.0
#declare -x DISPLAY="localhost:0.0"

# to get the effective root privilege for future uses
sudo ls

rm test_stderr.txt
touch test_stderr.txt
mkdir test_result

# cookie optimization off
./cookieopt.sh 0

TABFILES="tab_noopt0.py
tab_socket0.py
tab_whitelist0.py
tab_noopt1.py
tab_socket1.py
tab_whitelist1.py"

for i in $TABFILES; do
    cp ~/vcr/python-browser-8/$i ~/vcr/python-browser-8/tab.py
    rm ./test_stderr.txt
    ./test.sh
    mv ./test_stderr.txt ./test_result/$i
    killall test.sh
    sleep 5
done


# cookie optimization on
./cookieopt.sh 1

cp ~/vcr/python-browser-8/tab_whitelist0.py ~/vcr/python-browser-8/tab.py
rm ./test_stderr.txt
./test.sh
mv ./test_stderr.txt ./test_result/tab_cookieopt0.py

cp ~/vcr/python-browser-8/tab_whitelist1.py ~/vcr/python-browser-8/tab.py
rm ./test_stderr.txt
./test.sh
mv ./test_stderr.txt ./test_result/tab_cookieopt1.py







