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

int change_uid(int suid) {
  if(setgid(ROOT_UID)) {
    perror("setuid to root failed");
    return 1;
  }

  if(setgid(suid)) {
    perror("setgid failed");
    return 1;
  }

  if(setuid(suid)) {
    perror("setuid failed");
    return 1;
  }

  if(setegid(suid)) {
    perror("seteugid failed");
    return 1;
  }

  if(seteuid(suid)) {
    perror("seteuid failed");
    return 1;
  }

  return 0;
}
