(* test storing management *)
let test_holder = ref ([]:QCheck.Test.t list)

let add_test t = test_holder := t::(!test_holder)

let run_test () =
  QCheck_base_runner.run_tests ~colors:true ~verbose:false !test_holder

(* Type of random concretizations *)
type instance = (string * generable) list
and generable = GInt of int
              | GFloat of float

let mk_int x = GInt x
let mk_float x = GFloat x
