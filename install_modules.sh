#!/bin/bash

PWD=`pwd`
execcomm() {
    eval $1
    ec=$?
    if [ $ec -gt 0 ] ; then
	echo "An error occurs during installation. Please refer to the error messages above"
	exit $ec;
    fi    
}

execcomm "sudo apt-get install autoconf python-dev libxslt1-dev python-gtk2-dev libwebkitgtk-dev libsqlite3-dev gtk2-engines-pixbuf libgnome-keyring-dev coq ocaml python-xlib"

for i in {0..9}
do
    execcomm "sudo useradd tab$i"
done

execcomm "sudo useradd output"
xhost `whoami`

sudo groupadd quarkusers
sudo usermod -a -G quarkusers `whoami`
sudo usermod -g quarkusers `whoami`

cd $PWD

cd ./pywebkitgtk-1.1.8
execcomm "autoconf"
execcomm "automake"
execcomm "./configure"
execomm "make -j8"
execcomm "sudo make -j8 install"

cd $PWD

cd ./libsoup-2.34.0
execcomm "./configure"
execcomm "make -j8"
execcomm "sudo make -j8 install"

cd $PWD

mkdir $PWD

mkdir lib

cd ./lib
wget http://goto.ucsd.edu/quark/python-passfd-0.2.tar.gz
tar xvfz python-passfd-0.2.tar.gz
cd python-passfd-0.2
execcomm "make -j8"
execcomm "sudo make -j8 install"

cd $PWD

cd ./lib
wget http://goto.ucsd.edu/quark/shm-1.2.2.tar.gz
tar xvfz shm-1.2.2.tar.gz
cd shm-1.2.2
chmod +x setup.py
execcomm "sudo ./setup.py install"

cd $PWD

cd ./lib
wget http://goto.ucsd.edu/quark/Imaging-1.1.7.tar.gz
tar xvfz Imaging-1.1.7.tar.gz
cd Imaging-1.1.7
chmod +x setup.py
execcomm "sudo ./setup.py install"

cd $PWD

cd ./python-browser-8/
execcomm make

cd $PWD
cd ./kernel/
./install_ynot.sh
execcomm make buildall

