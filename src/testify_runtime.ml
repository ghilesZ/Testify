(* test storing management *)
let add_test,run_test =
  let holder = ref ([]:QCheck.Test.t list) in
  (fun t -> holder := t::(!holder)),
  (fun () -> QCheck_base_runner.run_tests ~colors:true ~verbose:false !holder)


(* abstract generators *)
(***********************)
type generable = GInt of int
               | GFloat of float

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
