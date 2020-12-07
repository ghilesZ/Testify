open Tools
open Apron

include Apronext.Apol

let manager = Polka.manager_alloc_strict ()

(* given a set of integer variables and a set of float variables,
   builds the unconstrained polyhedron defined on the given
   dimensions. Integers are bounded between Stdlib.min_int and
   Stdlib.max_int. Floats are bounded between Stdlib.min_float
   Stdlib.max_float *)
let init =
  let i = Interval.of_int min_int max_int in
  let f = Interval.of_float min_float max_float in
  fun ints reals ->
  let i_arr = SSet.to_seq ints |> Array.of_seq in
  let r_arr = SSet.to_seq reals |> Array.of_seq in
  let ivars = Array.map Var.of_string i_arr in
  let rvars =  Array.map Var.of_string r_arr in
  let env = Environment.make ivars rvars in
  let itvi = Array.map (fun _ -> i) i_arr in
  let itvr = Array.map (fun _ -> f) r_arr in
  let itvs = Array.concat [itvi; itvr] in
  let vars = Array.concat [ivars; rvars] in
  Abstract1.of_box manager env vars itvs

let split _ = failwith "poly.split"

let compile _ = failwith "poly.compile"

let filter _ = failwith "poly.filter"

let volume _ = failwith "poly.volume"
