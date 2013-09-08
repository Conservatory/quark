#!/usr/bin/env python

# Quark is Copyright (C) 2012-2015, Quark Team.
#
# You can redistribute and modify it under the terms of the GNU GPL,
# version 2 or later, but it is made available WITHOUT ANY WARRANTY.
#
# For more information about Quark, see our web site at:
# http://goto.ucsd.edu/quark/


import string
import sys
import subprocess
import select
import msg
import cPickle as pickle
import socket
import opt
import Cookie
import datetime
import urlparse

USER_AGENT = "Mozilla/5.0 (X11; Linux i686) AppleWebKit/534.30 (KHTML, like Gecko) Ubuntu/11.04 Chromium/12.0.742.112 Chrome/12.0.742.112 Safari/534.30"
COOKIE_FILE_NAME = "cookie-db"

# outputs a string to stderr of the kernel process.
def klog(str):
    klog_nonl(str + "\n")

def klog_nonl(str):
    sys.stderr.write("K: " + str)
    sys.stderr.flush()

# obsolete : 
def get_uri(uri):
    # The following would have avoived going to disk, but unfortunately,
    # wget does not perform link-conversion when outputting to stdout
    # html = subprocess.Popen(
    #     ['/usr/bin/wget',
    #      '-q',
    #      '--convert-links',
    #      '-O', '-',
    #      '-U', USER_AGENT,
    #      uri], 
    #     bufsize = 1, 
    #     stdin = subprocess.PIPE, 
    #     stdout = subprocess.PIPE).communicate()[0]
    result = subprocess.Popen(
        ['/usr/bin/wget',
         '--max-redirect=0',
	 '--tries=1',
	 '--timeout=1',
         #'-q',
         # '--convert-links',
         '-O', '-',
         '-U', USER_AGENT,
         uri],
        bufsize = -1,
        stdin = subprocess.PIPE, 
        stdout = subprocess.PIPE,
        stderr = subprocess.PIPE).communicate()
    err = result[1]
    err_split = string.split(err)
    l = len(err_split)
    if err_split[l-2] == "redirections" and err_split[l-1] == "exceeded.":
        content = "QUARK_REDIRECT " + err_split[l-5]
    else:
        content = result[0]
    return content

# an abstraction of wget which returns the contents of a web resource
# identified by uri in a form of string.
def get_uri_follow(uri):
    result = subprocess.Popen(
        ['/usr/bin/wget',
         '-q',
	 '--tries=1',
	 '--timeout=1',
         # '--convert-links',
         '-O', '-',
         '-U', USER_AGENT,
         uri],
        bufsize = -1,
        stdin = subprocess.PIPE, 
        stdout = subprocess.PIPE,
        stderr = subprocess.PIPE).communicate()
    content = result[0]
    return content

class PipedProcess:
   def __init__(self, kernel, pyfile, args):
       parent, child = socket.socketpair(msg.FAMILY, msg.TYPE)

       self.proc = subprocess.Popen(pyfile + [str(child.fileno())] + args + sys.argv[1:])
       self.soc = parent
       self.kernel = kernel

   def write_message(self, m):
       klog(">> " + str(m))
       msg.write_message_soc(m, self.soc)

   def read_message(self):
       m = msg.read_message_soc(self.soc)
       klog("<< " + str(m))
       return m

   def process_message(self, m):
       klog("ABSTRACT")

class CookieProcess(PipedProcess):
    def __init__(self, kernel, domain):
        PipedProcess.__init__(self, kernel, ["./cookie.py"], [domain])

class UIProcess(PipedProcess):
    def __init__(self, kernel):
        PipedProcess.__init__(self, kernel, ["./output.py"], [])

class TabProcess(PipedProcess):

    def get_trusted_origin_suffix(self) :
        sys.stdout.write("Enter trusted origin suffix(e.g, google.com): ")
        sys.stdout.flush()
        return sys.stdin.readline().strip()

    def __init__(self, kernel, init_url):
        subprocess.call(["/usr/bin/clear"])

        if init_url <> None:
            sys.stdout.write("the tab is navigated to " + init_url + "\n")
            self.tab_origin = self.get_trusted_origin_suffix()
            p1 = urlparse.urlparse(init_url)
            netloc = p1.netloc
            while netloc.endswith(self.tab_origin) == False:
                sys.stdout.write("The origin suffix you typed is inconsistent with the visiting url\n")
                self.tab_origin = self.get_trusted_origin_suffix()
        else:
            self.tab_origin = self.get_trusted_origin_suffix()
            init_url = "None"
                        
        PipedProcess.__init__(self, kernel, ["./tab.py"], [self.tab_origin, init_url])

    def process_message(self, m):
        if m.type == msg.mtypes.NAVIGATE:
            self.kernel.tabs[self.kernel.curr] =  TabProcess(self.kernel, m.uri)
            self.kernel.curr = len(self.kernel.tabs)-1
        if m.type == msg.mtypes.REQ_URI:
            self.kernel.ui.write_message(m)
            html = get_uri(m.uri)
            m = msg.create_res_uri(html)
            self.write_message(m)
        if m.type == msg.mtypes.REQ_URI_FOLLOW:
            self.kernel.ui.write_message(m)
            html = get_uri_follow(m.uri)
            m = msg.create_res_uri(html)
            self.write_message(m)
        elif m.type == msg.mtypes.DISPLAY:
            kernel = self.kernel
            tab_idx = kernel.find_tab_idx(self)
            if tab_idx == kernel.curr:
                m = msg.create_k2g_display(m.img)
                kernel.ui.write_message(m)
        elif m.type == msg.mtypes.DISPLAY_SHM:
            kernel = self.kernel
            tab_idx = kernel.find_tab_idx(self)
            if tab_idx == kernel.curr:
                m = msg.create_k2g_display_shm(m.shmid, m.size)
                kernel.ui.write_message(m)
        elif m.type == msg.mtypes.REQ_SOCKET:
            status_msg = msg.create_set_status("connecting to " + m.hostname)
            self.kernel.ui.write_message(status_msg)
            s = socket.socket(m.family, m.stype)
            if m.hostname.endswith(self.tab_origin) :
                s.connect((m.hostname, m.port))
            # if the hostname is not within the safe origin range, 
            # we return just a not-connected socket
            m = msg.create_res_socket(s.fileno())
            self.write_message(m)
        elif m.type == msg.mtypes.SET_COOKIE:
            self.kernel.add_cookie(m)
        elif m.type == msg.mtypes.GET_COOKIES:
            split = m.scheme_domain_path.split(";")
            cookies = self.kernel.get_cookies(m, split[0], split[1], split[2], bool(int(split[3])))
            m = msg.create_res_cookies(cookies)
            self.write_message(m)

    def render(self):
        self.write_message(msg.create_render())

class Kernel:
    def __init__(self):
        self.ui = UIProcess(self)
        self.tabs = []
        self.cookie_processes = {}
        self.curr = -1

    def curr_tab(self):
        return self.tabs[self.curr]

    def add_tab(self):
        self.tabs.append(TabProcess(self, None))
        self.curr = len(self.tabs)-1

    def switch_tab(self, tab_idx):
        if tab_idx < len(self.tabs):
            self.curr = tab_idx
            self.curr_tab().render()

    def mouse_click(self):
        p = subprocess.Popen(['./mousepos.py'], stdout = subprocess.PIPE)
        res = p.communicate()[0]
        (x, y) = pickle.loads(res)
        # res = p.communicate()[0].split(" ")
        # x = float(res[0])
        # y = float(res[1])
        t = self.curr_tab()
        t.write_message(msg.create_mouse_click(x,y))
        # t.write_message(msg.create_mouse_pressed(1,x,y))
        # t.write_message(msg.create_mouse_released(1,x,y))

    def find_process_from_chan(self, chan):
        procs = [self.ui] + self.tabs
        for p in procs:
            if p.soc == chan:
                return p

    def find_tab_idx(self, tab):
        return self.tabs.index(tab)

    def go(self, uri):
        self.curr_tab().write_message(msg.create_go(uri))

    def print_text_display(self):
        subprocess.call(["/usr/bin/clear"])
        def title(t, i):
            if i == self.curr:
                return "*" + t.tab_origin + "*"
            else:
                return t.tab_origin
        titles = map(title, self.tabs, range(len(self.tabs)))
        print "------------------------------------------------------------------------------------------------------------------------"
        print "| " + string.join(titles, " | ") + " |"
        print "------------------------------------------------------------------------------------------------------------------------"
        # for i in range(37):
        #     sys.stdout.write("\n")
        sys.stdout.write("Enter command: ")
        sys.stdout.flush()

    def get_tab_idx(self, ascii):
        if ascii >= 1 and ascii <=4:
            return ascii-1
        else:
            return None

    def process_input_char(self, c):
        #if c == 'g':
            #t = self.curr_tab()
            # t.write_message(msg.create_go("http://cseweb.ucsd.edu/~lerner/test1.html"))
            #t.write_message(msg.create_go("http://abc.go.com"))
            #t.write_message(msg.create_go("http://mail.eng.ucsd.edu"))
            #t.write_message(msg.create_go("http://www.google.com/ig"))
            #return

        ascii = ord(c)
        tab_idx = self.get_tab_idx(ascii)
        if tab_idx != None:
            self.switch_tab(tab_idx)
        elif ascii == 15: # F9
            self.exit()
        elif ascii == 16: # F10
            self.add_tab()
        elif ascii == 17: # F11
            self.add_tab()
        elif ascii == 18: # F12
            self.mouse_click()
        else:
            t = self.curr_tab()
            t.write_message(msg.create_key_press(c))

    def cookie_process_for_domain(self, domain):
        if domain in self.cookie_processes:
            return self.cookie_processes[domain]
        else:
            klog("Starting cookie process for domain: " + domain)
            c = CookieProcess(self, domain)
            self.cookie_processes[domain] = c
            return c

    def have_info_for_domain(self, domain):
        if domain in self.cookie_processes:
            return True
        try:
            f = open(domain)
            res = True
            f.close()
        except IOError as e:
            res = False
        return res

    # def cookies_for_domain(self, domain):
    #     if domain in self.cookie_db:
    #         return self.cookie_db[domain]
    #     else:
    #         cookies = Cookie.SimpleCookie()
    #         self.cookie_db[domain] = cookies
    #         return cookies

    # def add_cookie(self, cookie_str):
    #     def get_domain(cookie_str):
    #         c = Cookie.SimpleCookie()
    #         c.load(cookie_str)
    #         for name in c:
    #             return c[name]['domain']
    #     domain = get_domain(cookie_str)
    #     cookies = self.cookies_for_domain(domain)
    #     cookies.load(cookie_str)

    def add_cookie(self, m):
        def get_domain(cookie_str):
            c = Cookie.SimpleCookie()
            c.load(cookie_str)
            for name in c:
                return c[name]['domain']
        domain = get_domain(m.cookie)
        c = self.cookie_process_for_domain(domain)
        c.write_message(m)

    def get_cookies(self, m, scheme, domain, path, for_http):
        result_list = []
        def add_cookies_for_domain(domain):
            if self.have_info_for_domain(domain):
                c = self.cookie_process_for_domain(domain)
                c.write_message(m)
                response = c.read_message()
                assert(response.type == msg.mtypes.RES_COOKIES)
                if (response.cookies != " "):
                    result_list.append(response.cookies)
        # Comment and logic copied from libsoup:
	# The logic here is a little weird, but the plan is that if
	# domain is "www.foo.com", we will end up looking up cookies
	# for ".www.foo.com", "www.foo.com", ".foo.com", and ".com",
	# in that order. (Logic stolen from Mozilla.)
	l = domain.split(".")
        while l != []:
            domain_try = ".".join(l)
            # klog("Trying domain: ." + domain_try)
            add_cookies_for_domain("." + domain_try)
            if domain_try == domain:
                # klog("Trying domain: " + domain_try)
                add_cookies_for_domain(domain_try)
            l = l[1:]
        if result_list == []:
            return " "
        else:
            return '; '.join(result_list)

    def run(self):
        opt.parse_options(sys.argv[1:])
        while (True):
            self.print_text_display()
            chan_list = map(lambda x: x.soc, self.tabs)
            # klog("doing select...")
            (rs, _, _ ) = select.select(chan_list + [sys.stdin], [], [])
            # klog("after select...")
            if len(rs) > 0:
                chan_to_read = rs[0]
                if chan_to_read == sys.stdin:
                    c = sys.stdin.read(1)
                    self.process_input_char(c)
                else:
                    p = self.find_process_from_chan(chan_to_read)
                    m = p.read_message()
                    p.process_message(m)


    def exit(self):
        m = msg.create_exit()
        self.ui.write_message(m)
        for t in self.tabs:
            t.write_message(m)
        for (_,c) in self.cookie_processes.items():
            c.write_message(m)
        exit(0)

def cookie_expired(cookie):
    expires_str = cookie["expires"]
    if expires_str == "":
        # this is a session cookie, is not expired (will expire when
        # browser exits)
        return False
    else:
        expires = datetime.datetime.strptime(expires_str, "%a, %d-%b-%Y %H:%M:%S GMT")
        now = datetime.datetime.now()
        return expires < now

def cookie_expired_at_exit(cookie):
    expires_str = cookie["expires"]
    if expires_str == "":
        # this is a session cookie, it's expired since browser exits
        return True
    else:
        expires = datetime.datetime.strptime(expires_str, "%a, %d-%b-%Y %H:%M:%S GMT")
        now = datetime.datetime.now()
        return expires < now

def cookie_matches_scheme(cookie, scheme):
    return scheme == "https" or not cookie["secure"] == "true"
    
def cookie_matches_path(cookie, path):
    # following logic from soup_cookie_applies_to_uri in soup-cookie.c
    cookie_path = cookie["path"]
    if cookie_path == "":
        return True
    if not path.startswith(cookie_path):
        return False
    if not cookie_path.endswith("/") and len(path) > len(cookie_path) and path[len(cookie_path)] != "/":
        return False
    return True

def cookie_matches_for_http(cookie, for_http):
    return for_http or not cookie["httponly"] == "true"
    

def main():
    k = Kernel()
    k.run()

main()
