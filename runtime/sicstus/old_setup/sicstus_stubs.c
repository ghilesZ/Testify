#include <stdio.h>
#include <stdlib.h>

#define CAML_NAME_SPACE

#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/alloc.h>
#include <caml/custom.h>
#include <sicstus/sicstus.h>
#include <prt.h>

value to_caml_list(SP_term_ref seq){
  CAMLparam0 ();
  CAMLlocal1 (r);

  SP_term_ref head = SP_new_term_ref();
  SP_term_ref tail = SP_new_term_ref();
  int res = SP_get_list(seq, head, tail);
  if (res == 0)
    r = Val_emptylist;
  else {
    r = caml_alloc_small(2, 0);
    SP_integer itg;
    SP_get_integer(head, &itg);
    Field(r, 0) = Val_int(itg);
    Field(r, 1) = to_caml_list(tail);
  }
  CAMLreturn(r);
}

CAMLprim value stub_sicstus_get_increasing_list(value length, value seed){
  CAMLparam2(length, seed);
  SP_term_ref l = sicstus_increasing_list(Int_val(length), Int_val(seed));
  value lml = to_caml_list(l);
  // How to free l ? Can/Should we ?
  CAMLreturn(lml);
}

CAMLprim value stub_sicstus_get_decreasing_list(value length, value seed){
  CAMLparam2(length, seed);
  SP_term_ref l = sicstus_decreasing_list(Int_val(length), Int_val(seed));
  value lml = to_caml_list(l);
  CAMLreturn(lml);
}

CAMLprim value stub_sicstus_get_increasing_strict_list(value length, value seed){
  CAMLparam2(length, seed);
  SP_term_ref l = sicstus_increasing_strict_list(Int_val(length), Int_val(seed));
  value lml = to_caml_list(l);
  CAMLreturn(lml);
}

CAMLprim value stub_sicstus_get_decreasing_strict_list(value length, value seed){
  CAMLparam2(length, seed);
  SP_term_ref l = stub_sicstus_get_decreasing_strict_list(Int_val(length), Int_val(seed));
  value lml = to_caml_list(l);
  CAMLreturn(lml);
}

CAMLprim value stub_sicstus_get_alldiff_list(value length, value seed){
  CAMLparam2(length, seed);
  SP_term_ref l = sicstus_alldiff_list(Int_val(length), Int_val(seed));
  value lml = to_caml_list(l);
  CAMLreturn(lml);
}

CAMLprim value stub_sicstus_initialize(value unit) {
  sicstus_prt_initialize(0, NULL);
  return Val_unit;
}
