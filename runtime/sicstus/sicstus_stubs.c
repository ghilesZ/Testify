#include <stdio.h>

#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/alloc.h>
#include <caml/custom.h>

/* Placeholder */

#include <stdlib.h>

typedef struct l {
  int value;
  struct l *next;
} list;

list *init(int i, int length){
  if (length == 0){
    return NULL;
  } else {
    list* head = (list *)malloc(sizeof(list));
    head->value = i;
    head->next = init(i+1, length-1);
    return head;
  }
}

list *rev(list *l){
  list *r = NULL;
  list *succ = NULL;
  while (l != NULL){
    r = (list *)malloc(sizeof(list));
    r->next = succ;
    r->value = l->value;
    succ = r;
    l = l->next;
  }
  return r;
}

void destroy(list *l){
  list *r ;

  while (l != NULL){
    r = l;
    l = l->next;
    free(r);
  }
}

value to_caml_list(list *l){
  CAMLparam0 ();
  CAMLlocal1 (r);

  if (l == NULL){
    r = Val_emptylist;
  } else {
    r = caml_alloc_small(2, 0);
    Field(r, 0) = Val_int(l->value);
    Field(r, 1) = to_caml_list(l->next);
  }

  CAMLreturn(r);
}

/* End placeholder */

CAMLprim value stub_sicstus_get_increasing_list(value length, value seed){
  CAMLparam2(length, seed);
  list *l = init(1, Int_val(length));
  value lml = to_caml_list(l);
  destroy(l);
  CAMLreturn(lml);
}

CAMLprim value stub_sicstus_get_decreasing_list(value length, value seed){
  CAMLparam2(length, seed);
  list *l = init(1, Int_val(length));
  list *r = rev(l);
  free(l);
  value lml = to_caml_list(r);
  free(r);
  CAMLreturn(lml);
}

CAMLprim value stub_sicstus_get_increasing_strict_list(value length, value seed){
  return stub_sicstus_get_increasing_list(length,seed);
}

CAMLprim value stub_sicstus_get_decreasing_strict_list(value length, value seed){
  return stub_sicstus_get_decreasing_list(length,seed);
}

CAMLprim value stub_sicstus_get_alldiff_list(value length, value seed){
  return stub_sicstus_get_increasing_list(length,seed);
}
