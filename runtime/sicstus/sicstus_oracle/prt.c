// C APIs for  Path-oriented Random
// Author : Arnaud Gotlieb -- Simula Research Laboratory
// Ref: Path-oriented random testing,
//        Constraint reasonning in path-oriented random testing, A. Gotlieb and M. Petit, Proc of COMPSAC'2008
//        A. Gotlieb and M. Petit. An uniform random test data generator for path testing. Journal of Systems and Software, 83(12), Dec. 2010.
// Dates :
//              Feb. 2th, 2022: Testify integration
//
// Requires SICStus Prolog 3 (or higher) but only tested with 4.7.0 on WinXP
// Portability issue : lists:nth1 in Sicstus4, lists:nth in Sicstus3
// Validated using SICStus Prolog 4.7.0


#include <stdio.h>
#include <stdlib.h>
#include <sicstus/sicstus.h>
#include "prt.h"

SP_term_ref sicstus_increasing_list(sint n, sint g){
  SP_term_ref num, grain, seq;
  SP_pred_ref pred;
  SP_qid goal;
  if (!(pred = SP_predicate("sicstus_increasing_list", 3, "user"))) {   fprintf(stderr, " - Could not find sicstus_increasing_list/3.\n");  exit(1);  }
  SP_put_integer(num = SP_new_term_ref(), n);
  SP_put_integer(grain = SP_new_term_ref(), g);
  SP_put_variable(seq = SP_new_term_ref());
 if (!(goal = SP_open_query(pred, num, grain ,seq))) {   fprintf(stderr, " - Failed to open query.\n");  exit(1); }
  if (!(SP_next_solution(goal)==SP_SUCCESS)) { fprintf(stderr, " - Failed to find a solution.\n");  exit(1); }
  return(seq);
}

SP_term_ref sicstus_increasing_list_bounds(sint n, sint g, sint min, sint max){
  SP_term_ref num, grain, seq, minimum, maximum;
  SP_pred_ref pred;
  SP_qid goal;
  if (!(pred = SP_predicate("sicstus_increasing_list", 5, "user"))) {   fprintf(stderr, " - Could not find sicstus_increasing_list/5.\n");  exit(1);  }
  SP_put_integer(num = SP_new_term_ref(), n);
  SP_put_integer(grain = SP_new_term_ref(), g);
  SP_put_integer(minimum = SP_new_term_ref(), min);
  SP_put_integer(maximum = SP_new_term_ref(), max);
  SP_put_variable(seq = SP_new_term_ref());
  if (!(goal = SP_open_query(pred, num, grain, seq, minimum, maximum))) {   fprintf(stderr, " - Failed to open query.\n");  exit(1); }
  if (!(SP_next_solution(goal)==SP_SUCCESS)) { fprintf(stderr, " - Failed to find a solution.\n");  exit(1); }
  return(seq);
}

SP_term_ref sicstus_decreasing_list(sint n, sint g){
  SP_term_ref num, grain, seq;
  SP_pred_ref pred;
  SP_qid goal;
  if (!(pred = SP_predicate("sicstus_decreasing_list", 3, "user"))) {   fprintf(stderr, " - Could not find sicstus_decreasing_list/3.\n");  exit(1);  }
  SP_put_integer(num = SP_new_term_ref(), n);
  SP_put_integer(grain = SP_new_term_ref(), g);
  SP_put_variable(seq = SP_new_term_ref());
 if (!(goal = SP_open_query(pred, num, grain ,seq))) {   fprintf(stderr, " - Failed to open query.\n");  exit(1); }
  if (!(SP_next_solution(goal)==SP_SUCCESS)) { fprintf(stderr, " - Failed to find a solution.\n");  exit(1); }
  return(seq);
}

SP_term_ref sicstus_decreasing_list_bounds(sint n, sint g, sint min, sint max){
  SP_term_ref num, grain, seq, minimum, maximum;
  SP_pred_ref pred;
  SP_qid goal;
  if (!(pred = SP_predicate("sicstus_decreasing_list", 5, "user"))) {   fprintf(stderr, " - Could not find sicstus_decreasing_list/5.\n");  exit(1);  }
  SP_put_integer(num = SP_new_term_ref(), n);
  SP_put_integer(grain = SP_new_term_ref(), g);
   SP_put_integer(minimum = SP_new_term_ref(), min);
  SP_put_integer(maximum = SP_new_term_ref(), max);
  SP_put_variable(seq = SP_new_term_ref());
  if (!(goal = SP_open_query(pred, num, grain, seq, minimum, maximum))) {   fprintf(stderr, " - Failed to open query.\n");  exit(1); }
  if (!(SP_next_solution(goal)==SP_SUCCESS)) { fprintf(stderr, " - Failed to find a solution.\n");  exit(1); }
  return(seq);
}


SP_term_ref sicstus_increasing_strict_list(sint n, sint g){
  SP_term_ref num, grain, seq;
  SP_pred_ref pred;
  SP_qid goal;
  if (!(pred = SP_predicate("sicstus_increasing_strict_list", 3, "user"))) {   fprintf(stderr, " - Could not find sicstus_increasing_strict_list/3.\n");  exit(1);  }
  SP_put_integer(num = SP_new_term_ref(), n);
  SP_put_integer(grain = SP_new_term_ref(), g);
  SP_put_variable(seq = SP_new_term_ref());
 if (!(goal = SP_open_query(pred, num, grain ,seq))) {   fprintf(stderr, " - Failed to open query.\n");  exit(1); }
  if (!(SP_next_solution(goal)==SP_SUCCESS)) { fprintf(stderr, " - Failed to find a solution.\n");  exit(1); }
  return(seq);
}

SP_term_ref sicstus_increasing_strict_list_bounds(sint n, sint g, sint min, sint max){
  SP_term_ref num, grain, seq, minimum, maximum;
  SP_pred_ref pred;
  SP_qid goal;
  if (!(pred = SP_predicate("sicstus_increasing_strict_list", 5, "user"))) {   fprintf(stderr, " - Could not find sicstus_increasing_strict_list/5.\n");  exit(1);  }
  SP_put_integer(num = SP_new_term_ref(), n);
  SP_put_integer(grain = SP_new_term_ref(), g);
   SP_put_integer(minimum = SP_new_term_ref(), min);
  SP_put_integer(maximum = SP_new_term_ref(), max);
  SP_put_variable(seq = SP_new_term_ref());
  if (!(goal = SP_open_query(pred, num, grain, seq, minimum, maximum))) {   fprintf(stderr, " - Failed to open query.\n");  exit(1); }
  if (!(SP_next_solution(goal)==SP_SUCCESS)) { fprintf(stderr, " - Failed to find a solution.\n");  exit(1); }
  return(seq);
}

SP_term_ref sicstus_decreasing_strict_list(sint n, sint g){
  SP_term_ref num, grain, seq;
  SP_pred_ref pred;
  SP_qid goal;
  if (!(pred = SP_predicate("sicstus_decreasing_strict_list", 3, "user"))) {   fprintf(stderr, " - Could not find sicstus_decreasing_strict_list/3.\n");  exit(1);  }
  SP_put_integer(num = SP_new_term_ref(), n);
  SP_put_integer(grain = SP_new_term_ref(), g);
  SP_put_variable(seq = SP_new_term_ref());
 if (!(goal = SP_open_query(pred, num, grain ,seq))) {   fprintf(stderr, " - Failed to open query.\n");  exit(1); }
  if (!(SP_next_solution(goal)==SP_SUCCESS)) { fprintf(stderr, " - Failed to find a solution.\n");  exit(1); }
  return(seq);
}

SP_term_ref sicstus_decreasing_strict_list_bounds(sint n, sint g, sint min, sint max){
  SP_term_ref num, grain, seq, minimum, maximum;
  SP_pred_ref pred;
  SP_qid goal;
  if (!(pred = SP_predicate("sicstus_decreasing_strict_list", 5, "user"))) {   fprintf(stderr, " - Could not find sicstus_decreasing_strict_list/5.\n");  exit(1);  }
  SP_put_integer(num = SP_new_term_ref(), n);
  SP_put_integer(grain = SP_new_term_ref(), g);
   SP_put_integer(minimum = SP_new_term_ref(), min);
  SP_put_integer(maximum = SP_new_term_ref(), max);
  SP_put_variable(seq = SP_new_term_ref());
  if (!(goal = SP_open_query(pred, num, grain, seq, minimum, maximum))) {   fprintf(stderr, " - Failed to open query.\n");  exit(1); }
  if (!(SP_next_solution(goal)==SP_SUCCESS)) { fprintf(stderr, " - Failed to find a solution.\n");  exit(1); }
  return(seq);
}


SP_term_ref sicstus_alldiff_list(sint n, sint g){
  SP_term_ref num, grain, seq;
  SP_pred_ref pred;
  SP_qid goal;
  if (!(pred = SP_predicate("sicstus_alldiff_list", 3, "user"))) {   fprintf(stderr, " - Could not find sicstus_alldiff_list/3.\n");  exit(1);  }
  SP_put_integer(num = SP_new_term_ref(), n);
  SP_put_integer(grain = SP_new_term_ref(), g);
  SP_put_variable(seq = SP_new_term_ref());
 if (!(goal = SP_open_query(pred, num, grain ,seq))) {   fprintf(stderr, " - Failed to open query.\n");  exit(1); }
  if (!(SP_next_solution(goal)==SP_SUCCESS)) { fprintf(stderr, " - Failed to find a solution.\n");  exit(1); }
  return(seq);
}

SP_term_ref sicstus_alldiff_list_bounds(sint n, sint g, sint min, sint max){
  SP_term_ref num, grain, seq, minimum, maximum;
  SP_pred_ref pred;
  SP_qid goal;
  if (!(pred = SP_predicate("sicstus_alldiff_list", 5, "user"))) {   fprintf(stderr, " - Could not find sicstus_alldiff_list/5.\n");  exit(1);  }
  SP_put_integer(num = SP_new_term_ref(), n);
  SP_put_integer(grain = SP_new_term_ref(), g);
   SP_put_integer(minimum = SP_new_term_ref(), min);
  SP_put_integer(maximum = SP_new_term_ref(), max);
  SP_put_variable(seq = SP_new_term_ref());
  if (!(goal = SP_open_query(pred, num, grain, seq, minimum, maximum))) {   fprintf(stderr, " - Failed to open query.\n");  exit(1); }
  if (!(SP_next_solution(goal)==SP_SUCCESS)) { fprintf(stderr, " - Failed to find a solution.\n");  exit(1); }
  return(seq);
}

void sicstus_write_seq(SP_term_ref seq)
{
  SP_integer itg = 0;
  SP_term_ref
    tail = SP_new_term_ref(),
    via = SP_new_term_ref();
  SP_put_term(tail, seq);
  fprintf(stdout, "Generated random sequence:\n");
  while (SP_get_list(tail, via, tail)) { SP_get_integer(via, &itg);   fprintf(stdout, "%d; ", (int) itg); }
  fprintf(stdout, "\n\n");
}

void sicstus_prt_initialize(int argc, char **argv)
{
  sint rval;
  /* Initialize Prolog engine (SP_initialize) */
  if (SP_FAILURE == SP_initialize(argc, argv, NULL)) {  exit(1);  }

  /* Restore PRT from saved compiled/interpreted version prt.pl */
  rval = SP_restore("URL:x-sicstus-resource:/prt.sav");
  if (rval == SP_ERROR || rval == SP_FAILURE) exit(2);
}

void test(){
  SP_term_ref seq;
  sicstus_prt_initialize(0, NULL);
  SP_put_variable(seq = SP_new_term_ref());
  /* Test sicstus_increasing_list */
  seq = sicstus_increasing_list(10, 1); sicstus_write_seq(seq);
  seq = sicstus_increasing_list(10, 1); sicstus_write_seq(seq);
  seq = sicstus_increasing_list(5, 2); sicstus_write_seq(seq);
  seq = sicstus_increasing_list_bounds(15, 2, -25, 25); sicstus_write_seq(seq);
  seq = sicstus_increasing_list_bounds(10, 1, -100, 100); sicstus_write_seq(seq);
   //sicstus_increasing_list(1000000, 2); sicstus_write_seq(seq);

  /* Test sicstus_decreasing_list */
   seq = sicstus_decreasing_list(5, 2); sicstus_write_seq(seq);
   seq = sicstus_decreasing_list_bounds(10, 1, -100, 100); sicstus_write_seq(seq);

 /* Test sicstus_increasing_strict_list */
   seq = sicstus_increasing_strict_list(5, 1); sicstus_write_seq(seq);
   seq = sicstus_increasing_strict_list_bounds(10, 1, -100, 100); sicstus_write_seq(seq);

    /* Test sicstus_decreasing_strict_list */
   seq = sicstus_decreasing_strict_list(5, 1); sicstus_write_seq(seq);
   seq = sicstus_decreasing_strict_list_bounds(10, 1, -100, 100); sicstus_write_seq(seq);

   /* Test sicstus_alldiff_list */
   seq = sicstus_alldiff_list(5, 1); sicstus_write_seq(seq);
   seq = sicstus_alldiff_list_bounds(10, 1, -100, 100); sicstus_write_seq(seq);
   seq = sicstus_alldiff_list_bounds(20, 1, -5, 5); sicstus_write_seq(seq);
   // seq = sicstus_alldiff_list_bounds(20, 1, 5, -5); sicstus_write_seq(seq);
}
