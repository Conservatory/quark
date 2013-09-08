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

int main(int argc, char **argv) {
  // gets one argument, channel fd
  if (argc != 2) return -1;

  if (change_uid(OUTPUT_UID)) {
    perror("change uid failed");
    return -1;
  }
  fprintf(stderr, "output fd::%s:%d\n", argv[1], getuid());
  execl(OUTPUT_PROGRAM, OUTPUT_PROGRAM, argv[1], NULL);
  return 0;
}
