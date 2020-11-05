(** Example of compiling an abstract value of the interval abstract domain
    into a Parsetree.expression corresponding to a generator *)

open Migrate_parsetree
open Ast_410
open Ast_helper
open Helper
open Apron
open Apronext
module Conv = Convert (OCaml_410) (OCaml_current)

let manager = Polka.manager_alloc_strict ()

let ocaml_box =
  let i = Interval.of_int min_int max_int in
  let f = Interval.of_float min_float max_float in
  fun env ->
    let ivars, rvars = Environment.vars env in
    let vars = Array.concat [ivars; rvars] in
    let f v =
      match Environment.typ_of_var env v with INT -> i | REAL -> f
    in
    let itv_arr = Array.map f vars in
    Abstract1.of_box manager env vars itv_arr

let scalar_to_mpqf = function Scalar.Mpqf x -> x | _ -> assert false

(* compile an itv into a parsetree expression corresponding to a generator *)
let compile_itv typ (i : Interval.t) =
  let inf, sup = Interval.(scalar_to_mpqf i.inf, scalar_to_mpqf i.sup) in
  let body =
    match typ with
    | Environment.INT ->
        let i = inf |> Mpqf.to_float |> int_of_float |> int_exp in
        let s = sup |> Mpqf.to_float |> int_of_float |> int_exp in
        [exp_id "rs"]
        |> apply_nolbl (apply_runtime "int_range" [i; s])
        |> apply_runtime_1 "mk_int"
    | Environment.REAL ->
        let i = inf |> Mpqf.to_float |> float_exp in
        let s = sup |> Mpqf.to_float |> float_exp in
        [exp_id "rs"]
        |> apply_nolbl (apply_runtime "float_range" [i; s])
        |> apply_runtime_1 "mk_float"
  in
  lambda_s "rs" body

(** builds a Parsetree.expression corresponding to a box generator *)
let compile_box b =
  let env = b.Abstract1.env in
  let instance = ref empty_list_exp in
  Environmentext.iter
    (fun v ->
      let typ = Environment.typ_of_var env v in
      let i = Abstract1.bound_variable manager b v in
      let value = apply_nolbl (compile_itv typ i) [exp_id "rand_state"] in
      let pair = Exp.tuple [string_exp (Var.to_string v); value] in
      instance := cons_exp pair !instance)
    env ;
  lambda_s "rand_state" !instance
