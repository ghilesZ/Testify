(** {1 Global constraint} *)
open Helper

open Migrate_parsetree.Ast_410
open Parsetree

type t =
  { id: string  (** The name of the corresponding OCaml attribute *)
  ; value_provider: Location.t -> expression
        (** Ast for the value provider used during Boltzmann generation.
            Takes a location as an input for better error handling. *)
  ; checker: Location.t -> expression
        (** Ast for checking if a value satisfies the global constraint .*)
  ; group: int }

let print fmt {id; _} = Format.fprintf fmt "%s" id

(** {2 Pre-defined constraints} *)

let increasing =
  { id= "increasing"
  ; value_provider=
      (fun loc -> [%expr Testify_runtime.Sicstus.increasing_list])
  ; checker= (fun loc -> [%expr Testify_runtime.increasing])
  ; group= 0 }

let increasing_strict =
  { id= "increasing_strict"
  ; value_provider=
      (fun loc -> [%expr Testify_runtime.Sicstus.increasing_strict_list])
  ; checker= (fun loc -> [%expr Testify_runtime.increasing_strict])
  ; group= 0 }

let decreasing =
  { id= "decreasing"
  ; value_provider=
      (fun loc -> [%expr Testify_runtime.Sicstus.decreasing_list])
  ; checker= (fun loc -> [%expr Testify_runtime.decreasing])
  ; group= 0 }

let decreasing_strict =
  { id= "decreasing_strict"
  ; value_provider=
      (fun loc -> [%expr Testify_runtime.Sicstus.decreasing_strict_list])
  ; checker= (fun loc -> [%expr Testify_runtime.decreasing_strict])
  ; group= 0 }

let alldiff =
  { id= "alldiff"
  ; value_provider= (fun loc -> [%expr Testify_runtime.Sicstus.all_diff_list])
  ; checker= (fun loc -> [%expr Testify_runtime.alldiff])
  ; group= 0 }

let all =
  [alldiff; increasing; decreasing; increasing_strict; decreasing_strict]

(** Accepts global constraints of the form:

    - [@satisfying ID]
    - [@satisfying fun x -> ID x] where ID belongs to the list of predefined
      constraints `all`
    - [@satisfying fun x -> ID x && ID' x] where ID and ID' belongs to the
      list of predefined constraints `all` *)
(* todo handle lambdas correctly *)

let rec search (c : expression) : t list =
  match c.pexp_desc with
  | Pexp_ident id ->
      let id = Helper.lid_to_string id.txt in
      List.filter (fun gc -> gc.id = id) all
  | Pexp_fun (Nolabel, None, pat, body) -> (
    match (pat.ppat_desc, body.pexp_desc) with
    | ( Ppat_var arg
      , Pexp_apply
          ( {pexp_desc= Pexp_ident funname; _}
          , [ (Nolabel, {pexp_desc= Pexp_ident arg'; _})
            ; ( Nolabel
              , {pexp_desc= Pexp_constant (Pconst_integer (s, None)); _} ) ]
          ) ) ->
        let funname = Helper.lid_to_string funname.txt in
        let arg' = Helper.lid_to_string arg'.txt in
        if arg.txt = arg' then
          List.find_opt (fun gc -> gc.id = funname) all
          |> Option.to_list
          |> List.map (fun g -> {g with group= int_of_string s})
        else
          Format.asprintf "global constraint on unknown variable %s" arg'
          |> failwith
    | ( Ppat_var arg
      , Pexp_apply
          ( {pexp_desc= Pexp_ident funname; _}
          , [(Nolabel, {pexp_desc= Pexp_ident arg'; _})] ) ) ->
        let funname = Helper.lid_to_string funname.txt in
        let arg' = Helper.lid_to_string arg'.txt in
        if arg.txt = arg' then
          List.find_opt (fun gc -> gc.id = funname) all |> Option.to_list
        else
          Format.asprintf "global constraint on unknown variable %s" arg'
          |> failwith
    | ( Ppat_var _
      , Pexp_apply
          ( {pexp_desc= Pexp_ident {txt= Lident "&&"; _}; _}
          , [(Nolabel, arg1); (Nolabel, arg2)] ) ) ->
        search (lambda pat arg1) @ search (lambda pat arg2)
    | _ -> [] )
  | _ -> []
