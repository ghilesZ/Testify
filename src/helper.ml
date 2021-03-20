(* This module provides helpers for ast building *)

(* keep this before open as module Parse is shadowed by open
   Migrate_parsetree *)
let lparse s =
  try Parse.longident (Lexing.from_string s)
  with _ ->
    (* for operators *)
    Parse.longident (Lexing.from_string ("( " ^ s ^ " )"))

open Migrate_parsetree
open Ast_410
open Parsetree
open Asttypes
open Ast_helper

(* same as mkloc but with optional argument; default is Location.none*)
let none_loc ?(loc = Location.none) s = Location.mkloc s loc

(* builds a Longident.t Location.t from a string *)
let lid_loc ?(loc = Location.none) id = none_loc ~loc (lparse id)

(* pattern of string *)
let pat_s s = Pat.var (none_loc s)

(* given a string [name], builds the identifier [name] *)
let exp_id ?loc name = lid_loc ?loc name |> Exp.ident

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

(* opens the runtime and then build exp *)
let open_runtime exp =
  Exp.open_ (Opn.mk (Mod.ident (lid_loc "Testify_runtime"))) exp

(* calls a function defined in the runtime *)
let apply_runtime s = apply_nolbl_s ("Testify_runtime." ^ s)

(* apply_runtime for arity one functions *)
let apply_runtime_1 s x = apply_runtime s [x]

(* Same as Exp.fun_ *)
let lambda = Exp.fun_ Nolabel None

(* Same as lambda with string instead of pattern *)
let lambda_s = function "_" -> lambda (Pat.any ()) | s -> lambda (pat_s s)

(* function composition at ast level *)
let ( |><| ) f g = lambda_s "x" (apply_nolbl f [apply_nolbl g [exp_id "x"]])

(* doouble application *)
let ( @@@ ) f g e = apply_nolbl f [apply_nolbl g e]

(* boolean expressions *)
let true_ = Exp.construct (lid_loc "true") None

let false_ = Exp.construct (lid_loc "false") None

(* && over ast *)
let ( &&@ ) a b = apply_nolbl_s " (&&) " [a; b]

(* useful constructors *)
let int_ x = Exp.constant (Const.int x)

let one = int_ 1

let float_ x = Exp.constant (Const.float (string_of_float x))

let string_ x = Exp.constant (Const.string x)

let str_nonrec vb = Str.value Nonrecursive vb

let unit = Exp.construct (lid_loc "()") None

(* same as Exp.construct but with list of expressions *)
let constructor name params =
  Exp.construct (lid_loc name)
    (match params with [] -> None | [x] -> Some x | l -> Some (Exp.tuple l))

let pair a b = Exp.tuple [a; b]

(* value binding with string *)
let vb_s id exp = Vb.mk (pat_s id) exp

let let_ id exp in_ = Exp.let_ Nonrecursive [vb_s id exp] in_

(* ast for lists *)
let empty_list_exp = Exp.construct (lid_loc "[]") None

let cons_exp h t = Exp.construct (lid_loc "( :: )") (Some (Exp.tuple [h; t]))

let list_of_list l = List.fold_right cons_exp l empty_list_exp

(* fresh identifier generator *)
let id_gen_gen () =
  let cpt = ref 0 in
  fun () ->
    incr cpt ;
    let s = "x" ^ string_of_int !cpt in
    (s, exp_id s)

(* string concat with separator over ast expressions *)
let string_concat ?sep l =
  let sep = Option.value ~default:"" sep in
  apply_nolbl_s "String.concat" [string_ sep; list_of_list l]

(* map for type identifiers *)
module Types = Map.Make (struct
  type t = Longident.t

  let compare = compare
end)

let typ_var_of_ct ct =
  match ct.ptyp_desc with
  | Ptyp_var txt -> txt
  | _ -> invalid_arg "not a type variable"

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

(* fold_left over head and tail *)
let reduce f = function
  | [] -> invalid_arg "can not reduce an empty list"
  | h :: t -> List.fold_left f h t

let refine s f opt = Option.fold ~none:s ~some:f opt

(* printing *)

(* same as [pp], but in bold blue] *)
let bold_blue x = Format.asprintf "\x1b[34;1m%s\x1b[0m" x

(* same as [pp], but in blue *)
let blue x = Format.asprintf "\x1b[36m%s\x1b[0m" x

(* same as [pp], but in gray *)
let gray x = Format.asprintf "\x1b[37m%s\x1b[0m" x
