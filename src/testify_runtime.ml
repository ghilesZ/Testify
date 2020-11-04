(* test storing management *)
let add_test,run_test =
  let holder = ref ([]:QCheck.Test.t list) in
  (fun t -> holder := t::(!holder)),
  (fun () ->
    let holder = List.rev !holder in
    QCheck_base_runner.run_tests ~colors:true ~long:true ~verbose:true holder)

(* abstract generators handling *)

type generable = GInt of int | GFloat of float

let mk_int x = GInt x
let mk_float x = GFloat x

(* Type of random concretizations *)
type instance = (string * generable) list

let get_int name (l:instance) =
  match List.assoc name l with
  | GInt i -> i
  | _ -> failwith "type error"

let get_float name (l:instance) =
  match List.assoc name l with
  | GFloat f -> f
  | _ -> failwith "type error"

let int_range a b =
  if b < a then
    let msg = Format.asprintf "[%i;%i]" a b in
    invalid_arg ("invlid int_range: "^msg)
  else if a >= 0 || b <= 0 then (
    (* range smaller than max_int *)
    fun st -> a + (QCheck.Gen.int_bound (b-a) st)
  ) else (
    (* range potentially bigger than max_int: we split on 0 and
       choose the itv wrt to their size ratio *)
    fun st ->
    let f_a = float_of_int a in
    let ratio = (-.f_a) /. (float_of_int b -. f_a) in
    if Random.float 1. < ratio then - (QCheck.Gen.int_bound (abs a) st)
    else QCheck.Gen.int_bound b st
  )
