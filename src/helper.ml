(* This module provides helpers for ast building *)

open Migrate_parsetree
open Ast_410
open Parsetree
open Asttypes
open Ast_helper

(* same as mkloc but with optional argument; default is Location.none*)
let none_loc ?(loc = Location.none) s = Location.mkloc s loc

(* builds a Longident.t from a string *)
let lid (id : string) = Longident.Lident id

(* builds a Longident.t Location.t from a string *)
let lid_loc ?(loc = Location.none) id = none_loc ~loc (Longident.parse id)

let pat_s s = Pat.var (none_loc s)

(* given a string [name], builds the identifier [name] *)
let exp_id ?(loc = Location.none) name = lid_loc name |> Exp.ident ~loc

(* same as apply but argument are not labelled *)
let apply_nolbl f args = Exp.apply f (List.map (fun a -> (Nolabel, a)) args)

(* same as apply_nolbl but function name is a string *)
let apply_nolbl_s s = apply_nolbl (exp_id s)

(* same as [apply f args1@args2] where arguments in arg2 are not labelled *)
let apply_lab_nolab f args1 args2 =
  let labs = List.map (fun (s, e) -> (Labelled s, e)) args1 in
  let no_labs = List.map (fun a -> (Nolabel, a)) args2 in
  Exp.apply f (labs @ no_labs)

(* same as apply_lab_nolab but argument function name is a string *)
let apply_lab_nolab_s s = apply_lab_nolab (exp_id s)

(* calls a function defined in the runtime *)
let apply_runtime s = apply_nolbl_s ("Testify_runtime." ^ s)

(* apply_runtime for arity one functions *)
let apply_runtime_1 s x = apply_nolbl_s ("Testify_runtime." ^ s) [x]

(* Same as Exp.fun_ *)
let lambda = Exp.fun_ Nolabel None

(* Same as lambda with string instead of pattern *)
let lambda_s s = lambda (pat_s s)

(* function composition at ast level *)
let ( |><| ) f g = lambda_s "x" (apply_nolbl f [apply_nolbl g [exp_id "x"]])

(* doouble application *)
let ( @@@ ) f g e = apply_nolbl f [apply_nolbl g e]

(* application of bang *)
let bang = apply_nolbl_s "!"

(* application of := *)
let assign = apply_nolbl_s ":="

(* boolean expressions *)
let true_ = Exp.construct (lid_loc "true") None

let false_ = Exp.construct (lid_loc "false") None

(* useful constructors *)
let int_exp x = Exp.constant (Const.int x)

let float_exp x = Exp.constant (Const.float (string_of_float x))

let string_exp x = Exp.constant (Const.string x)

let str_nonrec vb = Str.value Nonrecursive vb

let unit = Exp.construct (lid_loc "()") None

(* easy value binding with string *)
let vb_s id exp = Vb.mk (pat_s id) exp

(* ast for lists *)
let empty_list_exp = Exp.construct (lid_loc "[]") None

let cons_exp h t = Exp.construct (lid_loc "::") (Some (Exp.tuple [h; t]))

(* fresh identifier generator *)
let get_name =
  let cpt = ref 0 in
  fun () ->
    incr cpt ;
    "x" ^ string_of_int !cpt

(* string concat with separator over ast expressions *)
let string_concat ?sep l =
  let sep =
    match sep with None -> string_exp "" | Some s -> string_exp s
  in
  let rec aux acc = function
    | [] -> acc
    | [last] -> apply_nolbl_s "^" [acc; last]
    | h :: tl ->
        let acc = apply_nolbl_s "^" [acc; h] in
        aux (apply_nolbl_s "^" [acc; sep]) tl
  in
  aux (string_exp "") l

(* map for type identifiers *)
module Types = Map.Make (struct
  type t = Longident.t

  let compare = compare
end)

(* zagreus *)
let add_s t_id = Types.add (Longident.Lident t_id)

let option_meet default o1 o2 f =
  match (o1, o2) with Some v1, Some v2 -> f v1 v2 | _ -> default

(* keeps the attributes with name 'n'*)
let check_attributes n attrs =
  List.filter (fun a -> a.attr_name.txt = n) attrs

(* gets the only attributes with name 'n', raises an error if more than one,
   None if 0 *)
let get_attribute_payload n attrs =
  match check_attributes n attrs with
  | [] -> None
  | [{attr_payload; _}] -> Some attr_payload
  | _ -> Format.asprintf "only one %s attribute accepted" n |> failwith

(* gets the pstr payload attached to an attribute *)
let get_attribute_pstr n attrs =
  match get_attribute_payload n attrs with
  | Some (PStr [{pstr_desc= Pstr_eval (e, _); _}]) -> Some e
  | Some _ -> Format.asprintf "bad %s attribute" n |> failwith
  | None -> None

module SSet = Set.Make (String)
module SMap = Map.Make (String)
