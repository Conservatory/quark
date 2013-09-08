#!/usr/bin/env python

# Quark is Copyright (C) 2012-2015, Quark Team.
#
# You can redistribute and modify it under the terms of the GNU GPL,
# version 2 or later, but it is made available WITHOUT ANY WARRANTY.
#
# For more information about Quark, see our web site at:
# http://goto.ucsd.edu/quark/


import sys
import gobject
import threading
import time
import gtk
from gtk import keysyms

def ilog(str):
    ilog_nonl(str + "\n")

def ilog_nonl(str):
    sys.stderr.write("I: " + str)
    sys.stderr.flush()

def write_str_stdout(s):
    for c in s:
        sys.stdout.write(c)
        sys.stdout.flush()
    sys.stdout.write('\n')
    sys.stdout.flush()

def write_char_stdout(c):
    sys.stdout.write(c)
    sys.stdout.flush()

def mouse_button_pressed(widget, event):
    if event.x < 100 and event.y < 50:
        gtk.gdk.pointer_ungrab()
        button.set_label("Grab Mouse")
    else:
        write_char_stdout(chr(18))

def mouse_button_released(widget, event):
    return

def start_clicked(widget):
    button.set_label("Ungrab")
    gtk.gdk.pointer_grab(win.get_window(),
                         False, 
                         gtk.gdk.BUTTON_PRESS_MASK |
                         gtk.gdk.BUTTON_RELEASE_MASK,
                         None,
                         None,
                         0L)

website = sys.argv[1]

time.sleep(1)
write_char_stdout(chr(17))
time.sleep(1)
write_str_stdout(website)
time.sleep(2)
write_str_stdout("\g http://" + website)
time.sleep(10)
gtk.main()

