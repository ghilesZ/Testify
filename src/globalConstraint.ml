(** {1 Global constraint} *)

open Migrate_parsetree.Ast_410
open Parsetree

type t =
  { id: string  (** The name of the corresponding OCaml attribute *)
  ; value_provider:
      Location.t -> Migrate_parsetree.Ast_410.Parsetree.expression
        (** Ast for the value provider used during Boltzmann generation.
            Takes a location as an input for better error handling. *) }

(** {2 Pre-defined constraints} *)

let increasing =
  { id= "increasing"
  ; value_provider=
      (fun loc ->
        [%expr
          fun nb_collect ->
            List.init nb_collect (fun _ -> Random.bits ())
            |> List.sort Int.compare] ) }

let make_not_implemented id =
  { id
  ; value_provider=
      (fun _loc ->
        Format.ksprintf failwith "Not implemented: global constraint \"%s\""
          id ) }

let all =
  [ make_not_implemented "alldiff"
  ; increasing
  ; make_not_implemented "decreasing"
  ; make_not_implemented "increasing_strict"
  ; make_not_implemented "decreasing_strict" ]

let search (c : expression) : t option =
  match c.pexp_desc with
  | Pexp_ident id ->
      let id = Helper.lid_to_string id.txt in
      List.find_opt (fun gc -> gc.id = id) all
  | Pexp_fun (Nolabel, None, pat, body) -> (
    match (pat.ppat_desc, body.pexp_desc) with
    | ( Ppat_var arg
      , Pexp_apply
          ( {pexp_desc= Pexp_ident funname; _}
          , [(Nolabel, {pexp_desc= Pexp_ident arg'; _})] ) ) ->
        let funname = Helper.lid_to_string funname.txt in
        if arg.txt = Helper.lid_to_string arg'.txt then
          List.find_opt (fun gc -> gc.id = funname) all
        else None
    | _ -> None )
  | _ -> None
