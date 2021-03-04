(* Generator generation *)

open Migrate_parsetree
open Ast_410
open Parsetree
open Ast_helper
open Helper
module Conv = Convert (OCaml_410) (OCaml_current)
module Solve = Cover.BoxCover
open Tools

(* exception we raise when we try to handle a term that does not belong to
   the subset of type langage we can handle *)
exception OutOfSubset of string

(* given a type 't' and a pattern, builds an exepression corresponding to a
   reconstruction function of type 'instance -> t' *)
(* TODO: handle more patterns (e.g. _, as) *)
let reconstruct core_type pattern =
  let rec aux int_set float_set ct pat =
    match (ct.ptyp_desc, pat.ppat_desc) with
    | Ptyp_constr ({txt= Lident "int"; _}, []), Ppat_var {txt= ptxt; _} ->
        let r = apply_nolbl_s "get_int" [string_exp ptxt] in
        (r, SSet.add ptxt int_set, float_set)
    | Ptyp_constr ({txt= Lident "float"; _}, []), Ppat_var {txt= ptxt; _} ->
        let r = apply_nolbl_s "get_float" [string_exp ptxt] in
        (r, int_set, SSet.add ptxt float_set)
    | Ptyp_tuple ttup, Ppat_tuple ptup ->
        let sons, i_s, f_s =
          List.fold_left2
            (fun (acc, i_s, f_s) tt pt ->
              let s', i_s, f_s = aux i_s f_s tt pt in
              (s' :: acc, i_s, f_s))
            ([], int_set, float_set) ttup ptup
        in
        let b =
          List.map (fun f -> apply_nolbl f [exp_id "i"]) (List.rev sons)
        in
        (lambda_s "i" (Exp.tuple b), i_s, f_s)
    | _ -> raise (OutOfSubset "core_type or pattern")
  in
  aux SSet.empty SSet.empty core_type pattern

(* fills the '_' of a pattern *)
let fill p =
  let get_name = id_gen_gen () in
  let rec aux p =
    match p.ppat_desc with
    (* we prefix the name with % to avoid ame clash *)
    | Ppat_any -> {p with ppat_desc= Ppat_var (none_loc ("%" ^ get_name ()))}
    | Ppat_var _ -> p
    | Ppat_tuple ptup -> {p with ppat_desc= Ppat_tuple (List.map aux ptup)}
    | _ -> raise (OutOfSubset "pattern")
  in
  aux p

let split_fun f =
  match f.pexp_desc with
  | Pexp_fun (Nolabel, None, pat, body) -> (pat, body)
  | _ ->
      Format.asprintf "was expecting a function but got %a"
        Pprintast.expression (Conv.copy_expression f)
      |> failwith

(* builds a generator list, sorted by probability of being chosen (from most
   likely to less likely) *)
let craft_generator name inner outer pattern r =
  let outer_gens =
    List.fold_left
      (fun acc (w, reject, g) ->
        let g =
          apply_nolbl_s "reject"
            [string_exp name; lambda pattern reject; r |><| g]
        in
        cons_exp (Exp.tuple [float_exp w; g]) acc)
      empty_list_exp (List.rev outer)
  in
  let inner_outer_gens =
    List.fold_left
      (fun acc (w, g) -> cons_exp (Exp.tuple [float_exp w; r |><| g]) acc)
      outer_gens (List.rev inner)
  in
  apply_nolbl_s "weighted" [inner_outer_gens] |> open_runtime

(* given a type declaration and a pattern, we build a generator *)
let abstract_core_type name td sat =
  let pat, body = split_fun sat in
  let pat' = fill pat in
  let r, i_s, f_s = reconstruct td pat' in
  let constr = Lang.of_ocaml body in
  let inner, outer = Solve.get_generators i_s f_s constr in
  craft_generator name inner outer pat' r

(* builds a generator *)
let generate t sat =
  try
    match t.ptype_kind with
    | Ptype_abstract -> (
      match t.ptype_manifest with
      | Some ct -> Some (abstract_core_type t.ptype_name.txt ct sat)
      | None -> None )
    | Ptype_variant _ -> None
    | Ptype_record _labs -> (* todo records *) None
    | Ptype_open -> None
  with OutOfSubset _ -> None
