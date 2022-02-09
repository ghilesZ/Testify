(** {1 Global constraint} *)

open Migrate_parsetree.Ast_410
open Parsetree

type t =
  { id: string  (** The name of the corresponding OCaml attribute *)
  ; value_provider: Location.t -> expression
        (** Ast for the value provider used during Boltzmann generation.
            Takes a location as an input for better error handling. *)
  ; checker: Location.t -> expression
        (** Ast for checking if a value satisfies the global constraint .*)
  }

(** {2 Pre-defined constraints} *)

let increasing =
  { id= "increasing"
  ; value_provider=
      (fun loc ->
        [%expr
          fun nb_collect ->
            List.init nb_collect (fun _ -> Random.int 100)
            |> List.sort Int.compare] )
  ; checker= (fun loc -> [%expr Testify_runtime.increasing]) }

let increasing_strict =
  { id= "increasing_strict"
  ; value_provider=
      (fun _loc ->
        Format.ksprintf failwith "Not implemented: global constraint \"%s\""
          "increasing_strict" )
  ; checker= (fun loc -> [%expr increasing_strict]) }

let decreasing =
  { id= "decreasing"
  ; value_provider=
      (fun _loc ->
        Format.ksprintf failwith "Not implemented: global constraint \"%s\""
          "decreasing" )
  ; checker= (fun loc -> [%expr decreasing]) }

let decreasing_strict =
  { id= "decreasing_strict"
  ; value_provider=
      (fun _loc ->
        Format.ksprintf failwith "Not implemented: global constraint \"%s\""
          "decreasing_strict" )
  ; checker= (fun loc -> [%expr decreasing_strict]) }

let alldiff =
  { id= "alldiff"
  ; value_provider=
      (fun loc ->
        [%expr
          fun nb_collect -> List.init nb_collect (fun _ -> Random.int 100)]
        )
  ; checker= (fun loc -> [%expr Testify_runtime.alldiff]) }

let make_not_implemented id =
  { id
  ; value_provider=
      (fun _loc ->
        Format.ksprintf failwith "Not implemented: global constraint \"%s\""
          id )
  ; checker=
      (fun _loc ->
        Format.ksprintf failwith "Not implemented: global constraint \"%s\""
          id ) }

let all =
  [alldiff; increasing; decreasing; increasing_strict; decreasing_strict]

(** Accepts global constraints of the form:

    - [@satisfying ID]
    - [@satisfying fun x -> ID x] where ID belongs to the list of predefined
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
          , [(Nolabel, {pexp_desc= Pexp_ident arg'; _})] ) ) ->
        let funname = Helper.lid_to_string funname.txt in
        if arg.txt = Helper.lid_to_string arg'.txt then
          List.filter (fun gc -> gc.id = funname) all
        else []
    | ( Ppat_var _arg
      , Pexp_apply
          ( {pexp_desc= Pexp_ident {txt= Lident "(&&)"; _}; _}
          , [(Nolabel, arg1); (Nolabel, arg2)] ) ) ->
        search arg1 @ search arg2
    | _ -> [] )
  | _ -> []
