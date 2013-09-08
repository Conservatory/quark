/*
  Quark is Copyright (C) 2012-2015, Quark Team.

  You can redistribute and modify it under the terms of the GNU GPL,
  version 2 or later, but it is made available WITHOUT ANY WARRANTY.

  For more information about Quark, see our web site at:
  http://goto.ucsd.edu/quark/
*/


#include <unistd.h>
#include <fcntl.h>
#include <stdio.h>
#include <sys/stat.h>
#include <sys/types.h>
#include "quarkexec.h"

#define UNSHARE  "/usr/bin/unshare"

int main(int argc, char **argv)
{
  int socketfd = atoi(argv[1]);
  int i=0;
  // close all file descriptors but the socket.
  for (i = getdtablesize(); i > 0; --i) {
    if (i != socketfd && i != 2) close(i);
  }

  execl(UNSHARE, UNSHARE, TAB_PROGRAM_GATE, "-n", argv[1], argv[2], argv[3], NULL);
  return 0;
}

