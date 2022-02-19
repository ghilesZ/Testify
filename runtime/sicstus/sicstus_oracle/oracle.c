#include <stdio.h>
#include <stdlib.h>
#include "prt.h"

#define MAX 128

#ifdef DEBUG
#define DEBUG_TEST 1
#else
#define DEBUG_TEST 0
#endif
#define LOG(X...)\
  do { if (DEBUG_TEST) fprintf(stderr, X); } while (0)

unsigned char buff[MAX];

void output_list(SP_term_ref list, int nb){
  SP_term_ref head = SP_new_term_ref();
  SP_term_ref tail = SP_new_term_ref();
  SP_integer itg;
  int i;
  for (i = 0; i < nb; i++){
    SP_get_list(list, head, tail);
    SP_get_integer(head, &itg);
    int j = write(1, &itg, 4);
    list = tail;
  }
  fflush(stdout);
  LOG("wrote %d bytes\n", nb * 4);
}

// writes length and seed
void setup (int fd, sint* length, sint* seed){
  int i = read(fd, buff, 4);
  *length = (buff[0] << 8) + buff[1];
  *seed = (buff[2] << 8) + buff[3];
}

// dispatch the request to the corresponding sictus functionnality
void answer(int fd){
  bzero(buff, MAX);
  int i = read(fd, buff, 1);
  sint length;
  sint seed;
  SP_term_ref list;
  switch(buff[0]){
  case 1:
    LOG("exiting\n");
    exit(0);
  case 2:
    setup(fd, &length, &seed);
    list = sicstus_increasing_list(length, seed);
    break;
  case 3:
    setup(fd, &length, &seed);
    list = sicstus_decreasing_list(length, seed);
    break;
  case 4:
    setup(fd, &length, &seed);
    list = sicstus_increasing_strict_list(length, seed);
    break;
  case 5:
    setup(fd, &length, &seed);
    list = sicstus_decreasing_strict_list(length, seed);
    break;
  case 6:
    setup(fd, &length, &seed);
    list = sicstus_alldiff_list(length, seed);
    break;
  default:
    LOG("unrecognized message %d\n", buff[0]);
    exit (0);
    break;
  }
  output_list(list, length);
  fflush(stdin);
}

// main loop
int user_main(int argc, char **argv){
  LOG("starting\n");
  sicstus_prt_initialize(argc, argv);
  for (;;){
    answer(0);
  }
  return 0;
}
