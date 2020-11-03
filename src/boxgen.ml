(** Exemple of compiling an abstract value of the interval abstract
   domain into a Parsetree.expression corresponding to a generator *)

open Migrate_parsetree
open Ast_410
open Ast_helper
open Helper

open Apron
open Apronext

module Conv = Convert (OCaml_410) (OCaml_current)

let manager = Polka.manager_alloc_strict()

let ocaml_box =
  let i = Interval.of_int min_int max_int in
  let f = Interval.of_float min_float max_float in
  fun env ->
  let ivars,rvars = Environment.vars env in
  let vars = Array.concat [ivars;rvars] in
  let map_itv v = match Environment.typ_of_var env v with INT -> i | REAL -> f in
  let itv_arr = Array.map map_itv vars in
  Abstract1.of_box manager env vars itv_arr

let scalar_to_mpqf = function
  | Scalar.Mpqf x -> x
  | _ -> assert false

(* compile an itv into a parsetree expression corresponding to a
   generator *)
let compile_itv typ (i:Interval.t) =
  let inf,sup = Interval.(scalar_to_mpqf i.inf, scalar_to_mpqf i.sup) in
  let body =
    match typ with
    | Environment.INT ->
       let inf = inf |> Mpqf.to_float |> int_of_float in
       let supf = sup |> Mpqf.to_float in
       let supi = supf |> int_of_float in
       let gen = apply_runtime "int_range" [int_exp inf; int_exp supi] in
       let r = apply_nolbl gen [exp_id "rand_state"] in
       apply_runtime "mk_int" [r]
    | Environment.REAL ->
       let size = Mpqf.sub sup inf |> Mpqf.to_float in
       let inf = inf |> Mpqf.to_float in
       let gen = apply_nolbl_s "QCheck.Gen.float_bound_inclusive" [float_exp 1.] in
       let value = apply_nolbl gen [exp_id "rand_state"] in
       let r = apply_nolbl_s "Float.mul" [value; float_exp size] in
       apply_runtime "mk_float" [apply_nolbl_s "Float.add" [float_exp inf; r]]
  in
  lambda_s "rand_state" body

(** builds a Parsetree.expression corresponding to a box generator *)
let compile_box b =
  let env = b.Abstract1.env in
  let instance = ref empty_list_exp in
  Environmentext.iter (fun v ->
      let typ = Environment.typ_of_var env v in
      let i = Abstract1.bound_variable manager b v in
      let value = apply_nolbl (compile_itv typ i) [exp_id "rand_state"] in
      let pair = Exp.tuple [string_exp (Var.to_string v);value] in
      instance:=cons_exp pair !instance
    ) env;
  lambda_s "rand_state" !instance
