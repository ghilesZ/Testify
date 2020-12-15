open Migrate_parsetree
open Ast_410
open Parsetree
open Ast_mapper
open Ast_helper
open Helper

let ocaml_version = Versions.ocaml_410

module Conv = Convert (OCaml_410) (OCaml_current)

(* given a label list '{x:int; y: float; ...}' and a boolean expression
   '(float x) < y', builds the predicate : 'fun {x;y;_} -> (float x) < y' *)
(* TODO: annotate the generated code to disable warning 27 locally *)
let handle_record labels e =
  let names =
    List.map
      (fun l ->
        (Location.mkloc (lparse l.pld_name.txt) l.pld_loc, Pat.var l.pld_name))
      labels
  in
  lambda (Pat.record names Closed) e

let unsugarize kind (attrs : attributes) =
  match kind with
  | Ptype_record records ->
      List.map
        (fun a ->
          if a.attr_name.txt = "s.t" then
            match a with
            | {attr_payload= PStr [{pstr_desc= Pstr_eval (e, _); _}]; _} ->
                let pred = handle_record records e in
                let payload = PStr [Str.eval pred] in
                Attr.mk (none_loc "satisfying") payload
            | _ -> failwith "bad s.t attribute"
          else a)
        attrs
  | _ -> attrs

let mapper =
  let handle_td _mapper ({ptype_kind; ptype_attributes; _} as td) =
    let satisfying_attribute = unsugarize ptype_kind ptype_attributes in
    {td with ptype_attributes= satisfying_attribute}
  in
  {default_mapper with type_declaration= handle_td}
