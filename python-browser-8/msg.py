# Quark is Copyright (C) 2012-2015, Quark Team.
#
# You can redistribute and modify it under the terms of the GNU GPL,
# version 2 or later, but it is made available WITHOUT ANY WARRANTY.
#
# For more information about Quark, see our web site at:
# http://goto.ucsd.edu/quark/


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

mtypes = enum(
              "K2G_DISPLAY_SHM",   # 8: K -> O
              "DISPLAY_SHM",       # 6: T -> K
              "REQ_URI_FOLLOW",    # 2: T -> K
              "REQ_SOCKET",        # 3: T -> K
              "RENDER",            # 4: K -> T
              "KEY_PRESS",         # 5: K -> T
              "MOUSE_CLICK",       # 6: I-> K, K -> T
              "RES_URI",           # 7: K -> T
              "RES_SOCKET",        # 8: K -> T
              "NAVIGATE",          # 9: K -> T
              "GET_COOKIE",        #10: T -> K
              "SET_COOKIE",        #11: T -> K
              "RES_COOKIE",        #12: K -> T
              "K2C_SET_COOKIE",    #13: K -> C
              "K2C_GET_COOKIE",    #14: K -> C
              "C2K_RES_COOKIE",    #15: C -> K
              "K2T_SET_COOKIE",    #16: K -> T
              "C2K_SET_COOKIE",    #17: C -> K
              
              # the following messages are NOT used anymore

              "GO",                # -1: I -> K, K -> T

              "REQ_URI",           # 2: T -> K              

              "K2G_DISPLAY",       # 0: K -> O
              "DISPLAY",           # 1: T -> K
              "NEW_TAB",           # 10: I -> K
              "SWITCH_TAB",        # 11: I -> K

              "SET_STATUS",        # 15: K -> O
              "SET_COOKIE",        # 16: T -> K
              "GET_COOKIES",       # 17: T -> K
              "RES_COOKIES",       # 18: K -> T
              "EXIT",
              )

class Message:
    def __init__(self, type):
        self.type = type

    def __str__(self):
        if self.type == mtypes.GO:
            return "GO(" + self.uri + ")"
        elif self.type == mtypes.REQ_URI:
            return "REQ_URI(" + self.uri + ")"
        elif self.type == mtypes.REQ_URI_FOLLOW:
            return "REQ_URI_FOLLOW(" + self.uri + ")"
        elif self.type == mtypes.RES_URI:
            return "RES_URI(...)"
        elif self.type == mtypes.RENDER:
            return "RENDER()"
        elif self.type == mtypes.DISPLAY:
            return "DISPLAY(...)"
        elif self.type == mtypes.DISPLAY_SHM:
            return "DISPLAY(...)"
        elif self.type == mtypes.K2G_DISPLAY:
            return "K2G_DISPLAY(...)"
        elif self.type == mtypes.K2G_DISPLAY_SHM:
            return "K2G_DISPLAY_SHM(" + str(self.shmid) + ", " \
                                      + str(self.size)  + ")"
        elif self.type == mtypes.MOUSE_CLICK:
            return "MOUSE_CLICK("   + str(self.x)      + ", " \
                                    + str(self.y)      + ")"
        # elif self.type == mtypes.MOUSE_PRESSED:
        #     return "MOUSE_PRESSED(" + str(self.button) + ", " \
        #                             + str(self.x)      + ", " \
        #                             + str(self.y)      + ")"
        # elif self.type == mtypes.MOUSE_RELEASED:
        #     return "MOUSE_RELEASED(" + str(self.button) + ", " \
        #                              + str(self.x)      + ", " \
        #                              + str(self.y)      + ")"
        elif self.type == mtypes.NEW_TAB:
            return "NEW_TAB()"
        elif self.type == mtypes.SWITCH_TAB:
            return "SWITCH_TAB(" + str(self.tab_idx) + ")"
        elif self.type == mtypes.KEY_PRESS:
            return "KEY_PRESS(" + str(self.key) + ")"
        elif self.type == mtypes.REQ_SOCKET:
            return "REQ_SOCKET(" + str(self.hostname) + ", " \
                                 + str(self.port)     + ", " \
                                 + str(self.family)   + ", " \
                                 + str(self.stype)    + ", " \
                                 + str(self.protocol) + ")"
        elif self.type == mtypes.RES_SOCKET:
            return "RES_SOCKET(" + str(self.socfd) + ")"
        elif self.type == mtypes.NAVIGATE:
            return "NAVIGATE(" + str(self.uri) + ")"
        elif self.type == mtypes.GET_COOKIE:
            return "GET_COOKIE(" + str(self.uri) + ")"
        elif self.type == mtypes.SET_COOKIE:
            return "SET_COOKIE(" + str(self.cookie) + ")"
        elif self.type == mtypes.RES_COOKIE:
            return "RES_COOKIE(" + str(self.cookie) + ")"
        elif self.type == mtypes.K2C_SET_COOKIE:
            return "K2C_SET_COOKIE(" + str(self.cookie) + ")"
        elif self.type == mtypes.K2C_GET_COOKIE:
            return "K2C_GET_COOKIE(" + str(self.tab_id) + "," + str(self.uri) + ")"
        elif self.type == mtypes.C2K_RES_COOKIE:
            return "C2K_RES_COOKIE(" + str(self.tab_id_cookie) + ")"
        elif self.type == mtypes.K2T_SET_COOKIE:
            return "K2T_SET_COOKIE(" + str(self.cookie) + ")"
        elif self.type == mtypes.C2K_SET_COOKIE:
            return "C2K_SET_COOKIE(" + str(self.cookie) + ")"
        elif self.type == mtypes.SET_STATUS:
            return "SET_STATUS(" + self.status + ")"
        elif self.type == mtypes.EXIT:
            return "EXIT()"

def create_go(uri):
    m = Message(mtypes.GO)
    m.uri = uri
    return m
    
def create_req_uri(uri):
    m = Message(mtypes.REQ_URI)
    m.uri = uri
    return m

def create_navigate(uri):
    m = Message(mtypes.NAVIGATE)
    m.uri = uri
    return m

def create_req_uri_follow(uri):
    m = Message(mtypes.REQ_URI_FOLLOW)
    m.uri = uri
    return m

def create_res_uri(content):
    m = Message(mtypes.RES_URI)
    m.content = content
    if m.content == None :
        m.content = ""
    return m

def create_render():
    return Message(mtypes.RENDER)

def create_display(img):
    m = Message(mtypes.DISPLAY)
    m.img = img
    return m

def create_display_shm(shmid, size):
    m = Message(mtypes.DISPLAY_SHM)
    m.shmid = shmid
    m.size = size
    return m

def create_k2g_display(img):
    m = Message(mtypes.K2G_DISPLAY)
    m.img = img
    return m

def create_k2g_display_shm(shmid, size):
    m = Message(mtypes.K2G_DISPLAY_SHM)
    m.shmid = shmid
    m.size = size
    return m

def create_mouse_click(x, y):
    m = Message(mtypes.MOUSE_CLICK)
    m.x = x
    m.y = y
    return m

# def create_mouse_pressed(button, x, y):
#     m = Message(mtypes.MOUSE_PRESSED)
#     m.button = button
#     m.x = x
#     m.y = y
#     return m

# def create_mouse_released(button, x, y):
#     m = Message(mtypes.MOUSE_RELEASED)
#     m.button = button
#     m.x = x
#     m.y = y
#     return m

def create_new_tab():
    m = Message(mtypes.NEW_TAB)
    return m

def create_switch_tab(tab_idx):
    m = Message(mtypes.SWITCH_TAB)
    m.tab_idx = tab_idx
    return m

def create_key_press(key):
    m = Message(mtypes.KEY_PRESS)
    m.key = key
    return m

def create_req_socket(hostname, port, family, stype, protocol):
    m = Message(mtypes.REQ_SOCKET)
    m.hostname = hostname
    m.port = port
    m.family = family
    m.stype = stype
    m.protocol = protocol
    return m

def create_res_socket(socfd):
    m = Message(mtypes.RES_SOCKET)
    m.socfd = socfd
    return m

def create_set_status(status):
    m = Message(mtypes.SET_STATUS)
    m.status = status
    return m

def create_get_cookie(uri):
    m = Message(mtypes.GET_COOKIE)
    m.uri = uri
    return m

def create_set_cookie(cookie):
    m = Message(mtypes.SET_COOKIE)
    m.cookie = cookie
    return m

def create_res_cookie(cookie):
    m = Message(mtypes.RES_COOKIE)
    m.cookie = cookie
    return m

def create_k2c_set_cookie(cookie):
    m = Message(mtypes.K2C_SET_COOKIE)
    m.cookie = cookie
    return m

def create_k2c_get_cookie(tab_id, uri):
    m = Message(mtypes.K2C_GET_COOKIE)
    m.tab_id = tab_id
    m.uri = uri
    return m

def create_c2k_res_cookie(tab_id_cookie):
    m = Message(mtypes.C2K_RES_COOKIE)
    m.tab_id_cookie = tab_id_cookie
    return m

def create_k2t_set_cookie(cookie):
    m = Message(mtypes.K2T_SET_COOKIE)
    m.cookie = cookie
    return m

def create_c2k_set_cookie(cookie):
    m = Message(mtypes.C2K_SET_COOKIE)
    m.cookie = cookie
    return m

def create_exit():
    m = Message(mtypes.EXIT)
    return m

#################################################################
#
# Read/Write messages
#
#################################################################

def read_message_soc(s):
    #if opt.options.use_length_encoding:
    return read_message_len(s)
    #else:
    #    return read_message_nt(s)

def write_message_soc(m, s):
    #if opt.options.use_length_encoding:
    write_message_len(m, s)
    #else:
    #    write_message_nt(m, s)


#################################################################
#
# Null terminated encoding
#
#################################################################

def read_nts(soc):
    s = ''
    c = soc.recv(1)
    while c != '\0':
        s += c
        c = soc.recv(1)
    return s

def read_message_nt(soc):
    s = read_nts(soc)
    if s == "Go":
        return create_go(read_nts(soc))
    elif s == "RequestHTML":
        return create_req_uri(read_nts(soc))
    elif s == "RequestHTMLFollow":
        return create_req_uri_follow(read_nts(soc))
    elif s == "ResultHTML":
        return create_res_uri(pickle.loads(read_nts(soc)))
    elif s == "RenderNow":
        return create_render()
    elif s == "Display":
        return create_display(pickle.loads(read_nts(soc)))
    elif s == "DisplayShm":
        (shmid, size) = pickle.loads(read_nts(soc))
        return create_display_shm(shmid, size)
    elif s == "K2GDisplay":
        return create_k2g_display(pickle.loads(read_nts(soc)))
    elif s == "K2GDisplayShm":
        (shmid, size) = pickle.loads(read_nts(soc))
        return create_k2g_display_shm(shmid, size)
    elif s == "MouseClick":
        (x, y) = pickle.loads(read_nts(soc))
        return create_mouse_click(x, y)
    # elif s == "MousePressed":
    #     (button, x, y) = pickle.loads(read_nts(soc))
    #     return create_mouse_pressed(button, x, y)
    # elif s == "MouseReleased":
    #     (button, x, y) = pickle.loads(read_nts(soc))
    #     return create_mouse_released(button, x, y)
    elif s == "NewTab":
        return create_new_tab()
    elif s == "SwitchTab":
        return create_switch_tab(int(read_nts(soc)))
    elif s == "KeyPress":
        return create_key_press(read_nts(soc)[0])
    elif s == "RequestSocket":
        msg = read_nts(soc)
        flds = string.split(msg, ":")
        hostname = flds[0]
        port = int(flds[1])
        family = int(flds[2])
        stype = int(flds[3])
        protocol = int(flds[4])
        return create_req_socket(hostname, port, family, stype, protocol)
    elif s == "SetStatus":
        return create_set_status(read_nts(soc))
    elif s == "SetCookie":
        return create_set_cookie(read_nts(soc))
    else:
        sys.stderr.write("LABEL ERROR: " + s + "\n")
        sys.stderr.flush()

def write_message_nt(m, soc):
    soc.sendall(nt_encoding(m))
    if m.type == mtypes.RES_SOCKET:
        passfd.sendfd(soc, m.socfd, message="\x00")

def nt_encoding(m):
    if m.type == mtypes.GO:
        return "Go\0" + m.uri + "\0"
    elif m.type == mtypes.REQ_URI:
        return "RequestHTML\0" + m.uri + "\0"
    elif m.type == mtypes.REQ_URI_FOLLOW:
        return "RequestHTMLFollow\0" + m.uri + "\0"
    elif m.type == mtypes.RES_URI:
        return "ResultHTML\0" + pickle.dumps(m.content) + "\0"
    elif m.type == mtypes.RENDER:
        return "RenderNow\0"
    elif m.type == mtypes.DISPLAY:
        img = pickle.dumps(m.img)
        if string.find(img, "\0") != -1:
            sys.stderr.write("PICKLE ERROR\n")
            sys.stderr.flush()
        return "Display\0" + img + "\0"
    elif m.type == mtypes.DISPLAY_SHM:
        return "DisplayShm\0" + \
            pickle.dumps((m.shmid, m.size)) + "\0"
    elif m.type == mtypes.K2G_DISPLAY:
        return "K2GDisplay\0" + pickle.dumps(m.img) + "\0"
    elif m.type == mtypes.K2G_DISPLAY_SHM:
        return "K2GDisplayShm\0" + \
            pickle.dumps((m.shmid, m.size)) + "\0"
    elif m.type == mtypes.MOUSE_CLICK:
        return "MouseClick\0" + \
            pickle.dumps((m.x, m.y)) + "\0"
    # elif m.type == mtypes.MOUSE_PRESSED:
    #     return "MousePressed\0" + \
    #            pickle.dumps((m.button, m.x, m.y)) + "\0"
    # elif m.type == mtypes.MOUSE_RELEASED:
    #     return "MouseReleased\0" + \
    #            pickle.dumps((m.button, m.x, m.y)) + "\0"
    elif m.type == mtypes.NEW_TAB:
        return "NewTab\0"
    elif m.type == mtypes.SWITCH_TAB:
        return "SwitchTab\0" + str(m.tab_idx) + "\0"
    elif m.type == mtypes.KEY_PRESS:
        return "KeyPress\0" + str(m.key) + "\0"
    elif m.type == mtypes.RES_SOCKET:
        return "ResultSocket\0"
    elif m.type == mtypes.SET_STATUS:
        return "SetStatus\0" + m.status + "\0"
    elif m.type == mtypes.SET_COOKIE:
        return "SetCookie\0" + m.cookie + "\0"

#################################################################
#
# Length encoding
#
#################################################################

def recv_exact(soc, size):
    buf = soc.recv(size)
    while len(buf) < size:
        buf = buf + soc.recv(size-len(buf))
    return buf

def read_lstr(soc):
    #print >> sys.stderr, "T: read_lstr: size buf is being read"
    size_buf = recv_exact(soc, 4)
    #print >> sys.stderr, "T: read_lstr: size buf is read:" 
    size = struct.unpack(">i", size_buf)[0]
    #print >> sys.stderr, "T: read_lstr: size is read:" + str(size)
    sys.stderr.flush()
    if size > 0 :
    	return recv_exact(soc, size)
    else: 
	str('\0')

def read_message_len(soc):
    
    msg_id = ord(soc.recv(1)[0])
    #print >> sys.stderr, "T: read_message_len msg_id:" + str(msg_id)

    if msg_id == mtypes.GO:
        return create_go(read_lstr(soc))
    elif msg_id == mtypes.REQ_URI:
        return create_req_uri(read_lstr(soc))
    elif msg_id == mtypes.NAVIGATE:
        return create_navigate(read_lstr(soc))
    elif msg_id == mtypes.REQ_URI_FOLLOW:
        return create_req_uri_follow(read_lstr(soc))
    elif msg_id == mtypes.RES_URI:
        #return create_res_uri(pickle.loads(read_lstr(soc)))
        return create_res_uri(read_lstr(soc))
    #elif msg_id == mtypes.RES_SOCKET:
        #print >> sys.stderr, "T: res_socket:" + str(msg_id)
        #sys.stderr.flush()
        #return create_res_socket(read_lstr(soc))
        #dummy = read_lstr(soc)
        #print >> sys.stderr, "T: res_socket dummy:" + str(dummy)
        #sys.stderr.flush()
        #return create_res_socket(passfd.recvfd(soc))
    elif msg_id == mtypes.RENDER:
        dummy = read_lstr(soc)
        return create_render()
    elif msg_id == mtypes.DISPLAY:
        return create_display(pickle.loads(read_lstr(soc)))
    elif msg_id == mtypes.DISPLAY_SHM:
        (shmid, size) = pickle.loads(read_lstr(soc))
        return create_display_shm(shmid, size)
    elif msg_id == mtypes.K2G_DISPLAY:
        return create_k2g_display(pickle.loads(read_lstr(soc)))
    elif msg_id == mtypes.K2G_DISPLAY_SHM:
        (shmid, size) = pickle.loads(read_lstr(soc))
        return create_k2g_display_shm(shmid, size)
    elif msg_id == mtypes.MOUSE_CLICK:
        (x, y) = pickle.loads(read_lstr(soc))
        return create_mouse_click(x, y)
    # elif msg_id == mtypes.MousePressed:
    #     (button, x, y) = pickle.loads(read_lstr(soc))
    #     return create_mouse_pressed(button, x, y)
    # elif msg_id == mtypes.MouseReleased:
    #     (button, x, y) = pickle.loads(read_lstr(soc))
    #     return create_mouse_released(button, x, y)
    elif msg_id == mtypes.NEW_TAB:
        dummy = read_lstr(soc)
        return create_new_tab()
    elif msg_id == mtypes.SWITCH_TAB:
        return create_switch_tab(int(read_lstr(soc)))
    elif msg_id == mtypes.KEY_PRESS:
        return create_key_press(read_lstr(soc)[0])
    elif msg_id == mtypes.REQ_SOCKET:
        msg = read_lstr(soc)
        flds = string.split(msg, ":")
        hostname = flds[0]
        port = int(flds[1])
        family = int(flds[2])
        stype = int(flds[3])
        protocol = int(flds[4])
        return create_req_socket(hostname, port, family, stype, protocol)
    elif msg_id == mtypes.SET_STATUS:
        return create_set_status(read_lstr(soc))
    elif msg_id == mtypes.GET_COOKIE:
        return create_get_cookie(read_lstr(soc))
    elif msg_id == mtypes.SET_COOKIE:
        return create_set_cookie(read_lstr(soc))
    elif msg_id == mtypes.RES_COOKIE:
        return create_res_cookie(read_lstr(soc))
    elif msg_id == mtypes.K2C_SET_COOKIE:
        return create_k2c_set_cookie(read_lstr(soc))
    elif msg_id == mtypes.K2C_GET_COOKIE:
        raw_payload = read_lstr(soc)
        tab_id = raw_payload[0:4]
        uri = raw_payload[4:]
        return create_k2c_get_cookie(tab_id, uri)
    elif msg_id == mtypes.K2C_SET_COOKIE:
        return create_k2c_set_cookie(read_lstr(soc))
    elif msg_id == mtypes.C2K_RES_COOKIE:
        return create_c2k_res_cookie(read_lstr(soc))
    elif msg_id == mtypes.K2T_SET_COOKIE:
        return create_k2t_set_cookie(read_lstr(soc))
    elif msg_id == mtypes.C2K_SET_COOKIE:
        return create_c2k_set_cookie(read_lstr(soc))
    elif msg_id == mtypes.EXIT:
        dummy = read_lstr(soc)
        return create_exit()
    else:
        sys.stderr.write("LABEL ERROR: " + str(msg_id) + "\n")
        sys.stderr.flush()

def write_message_len(m, soc):
    soc.sendall(len_encoding(m))
    if m.type == mtypes.RES_SOCKET:
        passfd.sendfd(soc, m.socfd, message="\x00")

def len_encoding(m):
    payld = payload(m)
    #print >> sys.stderr, "T:: BEGIN sent msg: " + str(m) 
    #print >> sys.stderr, "T:: END   sent msg payload size:" + str(len(payld)) + ",tag:" + str(m.type)
    return chr(m.type) + struct.pack(">i", len(payld)) + payld

def payload(m):
    if m.type == mtypes.GO:
        return m.uri
    elif m.type == mtypes.REQ_URI:
        return m.uri
    elif m.type == mtypes.NAVIGATE:
        return m.uri
    elif m.type == mtypes.REQ_URI_FOLLOW:
        return m.uri
    elif m.type == mtypes.RES_URI:
        return pickle.dumps(m.content)
    elif m.type == mtypes.RENDER:
        return "\0"
    elif m.type == mtypes.DISPLAY:
        img = pickle.dumps(m.img)
        return img
    elif m.type == mtypes.DISPLAY_SHM:
        return pickle.dumps((m.shmid, m.size))
    elif m.type == mtypes.K2G_DISPLAY:
        return pickle.dumps(m.img)
    elif m.type == mtypes.K2G_DISPLAY_SHM:
        return pickle.dumps((m.shmid, m.size))
    elif m.type == mtypes.MOUSE_CLICK:
        return pickle.dumps((m.x, m.y))
    # elif m.type == mtypes.MOUSE_PRESSED:
    #     return "MousePressed\0" + \
    #            pickle.dumps((m.button, m.x, m.y)) + "\0"
    # elif m.type == mtypes.MOUSE_RELEASED:
    #     return "MouseReleased\0" + \
    #            pickle.dumps((m.button, m.x, m.y)) + "\0"
    elif m.type == mtypes.NEW_TAB:
        return "\0"
    elif m.type == mtypes.SWITCH_TAB:
        return str(m.tab_idx)
    elif m.type == mtypes.KEY_PRESS:
        return str(m.key)
    elif m.type == mtypes.RES_SOCKET:
        return "\0"
    elif m.type == mtypes.SET_STATUS:
        return m.status
    elif m.type == mtypes.GET_COOKIE:
        return m.uri
    elif m.type == mtypes.SET_COOKIE:
        return m.cookie
    elif m.type == mtypes.RES_COOKIES:
        return m.cookie
    elif m.type == mtypes.K2C_SET_COOKIE:
        return m.cookie
    elif m.type == mtypes.K2C_GET_COOKIE:
        return str(m.tab_id) + str(m.uri)
    elif m.type == mtypes.C2K_RES_COOKIE:
        return str(m.tab_id_cookie)
    elif m.type == mtypes.K2T_SET_COOKIE:
        return m.cookie
    elif m.type == mtypes.C2K_SET_COOKIE:
        return m.cookie
    elif m.type == mtypes.EXIT:
        return "\0"
