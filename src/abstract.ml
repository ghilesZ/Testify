(** Exemple of compiling an abstract value of the interval abstract
   domain into a Parsetree.expression corresponding to a generator *)

open Migrate_parsetree
open Ast_410
open Parsetree
open Ast_mapper
open Ast_helper
open Helper
open Apron

let s_to_mpqf = let open Scalar in function
  | Mpqf x -> x
  | Float x -> Mpqf.of_float x
  | Mpfrf x -> Mpfrf.to_mpqf x

let itv_to_mpqf i = Interval.(s_to_mpqf i.inf,s_to_mpqf i.sup)

let compile_itv typ (i:Interval.t) =
  let inf,sup = itv_to_mpqf i in
  match typ with
  | Environment.INT ->
     let size = Mpqf.sub sup inf |> Mpqf.to_float |> ceil |> int_of_float in
     let size = size+1 in
     let inf = inf |> Mpqf.to_float |> ceil |> int_of_float in
     let body =
       let r = apply_nolbl_s "Gen.int_bound" [int_exp size] in
       apply_nolbl_s "+" [int_exp inf; r]
     in
     Exp.fun_ Nolabel None (pat_s "x") body
  | Environment.REAL ->
     let size = Mpqf.sub sup inf |> Mpqf.to_float in
     let inf = inf |> Mpqf.to_float in
     let body =
       let r = apply_nolbl_s "Gen.float_bound_exclusive" [float_exp 1.] in
       let r = apply_nolbl_s "*." [r; float_exp size] in
       apply_nolbl_s "+." [float_exp inf; r]
     in
     Exp.fun_ Nolabel None (pat_s "x") body

let compile_box _b = assert false
