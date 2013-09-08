
import cPickle as pickle
import string
import sys
import socket
import struct
import opt
import passfd

FAMILY = socket.AF_UNIX
TYPE   = socket.SOCK_STREAM

def enum(*sequential, **named):
    enums = dict(zip(sequential, range(len(sequential))), **named)
    return type('Enum', (), enums)


mtypes = enum("GO",                # 0: I -> K, K -> T
              "REQ_URI",           # 1: T -> K
              "REQ_URI_FOLLOW",    # 2: T -> K
              "RES_URI",           # 3: K -> T
              "RENDER",            # 4: K -> T
              "DISPLAY",           # 5: T -> K
              "DISPLAY_SHM",       # 6: T -> K
              "K2G_DISPLAY",       # 7: K -> O
              "K2G_DISPLAY_SHM",   # 8: K -> O
              "MOUSE_CLICK",       # 9: I-> K, K -> T
              "NEW_TAB",           # 10: I -> K
              "SWITCH_TAB",        # 11: I -> K
              "KEY_PRESS",         # 12: K -> T
              "REQ_SOCKET",        # 13: T -> K
              "RES_SOCKET",        # 14: K -> T
              "SET_STATUS",        # 15: K -> O
              "SET_COOKIE",        # 16: T -> K
              "GET_COOKIES",       # 17: T -> K
              "RES_COOKIES",       # 18: K -> T
              )

print mtypes.GO
