(* This module provides helpers for ast building *)

open Migrate_parsetree
open Ast_408
open Asttypes
open Ast_helper

(* same as mkloc but with optional argument; default is Location.none*)
let none_loc ?loc:(loc=Location.none) s =
  Location.mkloc s loc

(* builds a Longident.t Location.t for a string *)
let lid ?loc:(loc=Location.none) id =
  none_loc ~loc (Longident.parse id)

(* given a string [name], builds the identifier [name] *)
let exp_id ?loc:(loc=Location.none) name =
  lid name |> Exp.ident ~loc

(* same as apply but argument are not labelled *)
let apply_nolbl f args =
  Exp.apply f (List.map (fun a -> Nolabel,a) args)

(* same as apply_nolbl but argument function name is a string *)
let apply_nolbl_s s = apply_nolbl (exp_id s)

(* same as [apply f args1@args2] where arguments in arg2 are not labelled *)
let apply_lab_nolab f args1 args2 =
  let labs = List.map (fun (s,e) -> Labelled s,e) args1 in
  let no_labs = List.map (fun a -> Nolabel,a) args2 in
  Exp.apply f (labs@no_labs)

(* same as apply_lab_nolab but argument function name is a string  *)
let apply_lab_nolab_s s =
  apply_lab_nolab (exp_id s)

(* application of bang *)
let bang = apply_nolbl_s "!"

(* application of := *)
let assign = apply_nolbl_s ":="

(* boolean expressions *)
let true_exp = Exp.construct (lid "true") None
let false_exp = Exp.construct (lid "false") None

(* useful constructors *)
let int_exp x = Exp.constant (Const.int x)
let string_exp x = Exp.constant (Const.string x)
let str_nonrec vb = Str.value Nonrecursive vb
