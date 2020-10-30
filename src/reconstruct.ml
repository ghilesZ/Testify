open Migrate_parsetree
open Ast_410
open Parsetree
open Ast_mapper
open Ast_helper
open Helper

(* Parsetree.expression of type 'instance -> int' or 'instance -> float' *)
let constructors =
  Types.empty
  |> add_s "int" (fun v -> apply_nolbl_s "Testify_runtime.get_int" [string_exp v])
  |> add_s "float" (fun v -> apply_nolbl_s "Testify_runtime.get_float" [string_exp v])

let reconstruct core_type pattern =
  let rec aux ct pat =
    match ct.ptyp_desc,pat.ppat_desc with
    | Ptyp_constr({txt;_},[]), Ppat_var {txt=ptxt;_} ->
       (Types.find txt constructors) ptxt
    | Ptyp_tuple ttup, Ppat_tuple ptup ->
       let sons = List.map2 aux ttup ptup in
       let body = List.map (fun f -> apply_nolbl f [exp_id "i"]) sons in
       Exp.fun_ Nolabel None (pat_s "i") (Exp.tuple body)
    | _ -> assert false
  in
  aux core_type pattern
