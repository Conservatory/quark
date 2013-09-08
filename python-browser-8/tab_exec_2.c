#include <unistd.h>
#include <fcntl.h>
#include <stdio.h>
#include <sys/stat.h>
#include <sys/types.h>
#include "quarkexec.h"
 
int main(int argc, char **argv)
{
  // gets 3 arguments. 1: channel fd 2: tab user id 3: start URL
  if (argc != 4) return 1;
  int suid = atoi(argv[2]);
  if (change_uid(suid)) {
    perror("change uid failed");
    return -1;
  }
  execl(TAB_PROGRAM, TAB_PROGRAM, argv[1], argv[3], NULL);
  return 0;
}

