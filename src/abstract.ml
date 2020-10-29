(** Exemple of compiling an abstract value of the interval abstract
   domain into a Parsetree.expression corresponding to a generator *)

open Migrate_parsetree
open Ast_410
open Ast_helper
open Helper
open Apron

module Conv = Convert (OCaml_410) (OCaml_current)

let manager = Box.manager_alloc()

let s_to_mpqf = let open Scalar in function
                                | Mpqf x -> x
                                | Float x -> Mpqf.of_float x
                                | Mpfrf x -> Mpfrf.to_mpqf x

let itv_to_mpqf i = Interval.(s_to_mpqf i.inf,s_to_mpqf i.sup)

(* compile an itv into a parsetree expression corresponding to a
   generator *)
let compile_itv typ (i:Interval.t) =
  let inf,sup = itv_to_mpqf i in
  match typ with
  | Environment.INT ->
     let size = Mpqf.sub sup inf |> Mpqf.to_float |> ceil |> int_of_float in
     let size = size+1 in
     let inf = inf |> Mpqf.to_float |> ceil |> int_of_float in
     let body =
       let gen = apply_nolbl_s "QCheck.Gen.int_bound" [int_exp size] in
       let r = apply_nolbl gen [exp_id "rand_state"] in
       apply_nolbl_s "mk_int" [apply_nolbl_s "+" [int_exp inf; r]]
     in
     Exp.fun_ Nolabel None (pat_s "rand_state") body
  | Environment.REAL ->
     let size = Mpqf.sub sup inf |> Mpqf.to_float in
     let inf = inf |> Mpqf.to_float in
     let body =
       let gen = apply_nolbl_s "QCheck.Gen.float_bound_inclusive" [float_exp 1.] in
       let value = apply_nolbl gen [exp_id "rand_state"] in
       let r = apply_nolbl_s "Float.mul" [value; float_exp size] in
       apply_nolbl_s "mk_float" [apply_nolbl_s "Float.add" [float_exp inf; r]]
     in
     Exp.fun_ Nolabel None (pat_s "rand_state") body

(** builds a Parsetree.expression corresponding to a generator from a
   box *)
let compile_box b =
  let box = Abstract1.to_box manager b in
  let env = box.Abstract1.box1_env in
  let itvs = box.Abstract1.interval_array in
  let instance,_ =
    Array.fold_left (fun (acc,idx) i ->
        let v = Environment.var_of_dim env idx in
        let typ = Environment.typ_of_var env v in
        let value = apply_nolbl (compile_itv typ i) [exp_id "rand_state"] in
        let pair = Exp.tuple [string_exp (Var.to_string v);value] in
        let instance = cons_exp pair acc in
        instance,(idx+1)
      ) (empty_list_exp,0) itvs
  in
  Exp.fun_ Nolabel None (pat_s "rand_state") instance

let _ =
  let vx = Var.of_string "x" in
  let vy = Var.of_string "y" in
  let env = Environment.make [||] [|vx;vy|] in
  let box = Abstract1.top manager env in
  let texpr1 = Texpr1.cst env (Coeff.i_of_int (-3) 5) in
  let texpr2 = Texpr1.cst env (Coeff.i_of_int 2 18) in
  let box = Abstract1.assign_texpr manager box vx texpr1 None in
  let box = Abstract1.assign_texpr manager box vy texpr2 None in
  let ast = compile_box box in
  Format.printf "%a\n%!" Pprintast.expression (Conv.copy_expression ast)
