#!/usr/bin/python

from ctypes import *
libsoup = CDLL("libsoup-2.4.so.1")
libsoup.soup_set_t2k_raw_socket(5);

