open Migrate_parsetree
open Ast_410
open Parsetree
open Ast_mapper
open Ast_helper
open Helper

let ocaml_version = Versions.ocaml_410
module Conv = Convert (OCaml_410) (OCaml_current)

(* given a label list '{x:int; y: float; ...}' and a boolean expression
   '(float x) < y', builds the predicate : 'fun {x;y;_} -> (float x) < y'*)
let handle_record labels _e =
  let _names = List.map (fun l -> l.pld_name.txt) labels in
  assert false

let unsugarize kind (attrs:attributes) =
  match kind with
  | Ptype_record records ->
     (match List.filter (fun a -> a.attr_name.txt = "s.t") attrs with
      | [] -> attrs
      | [{attr_payload=PStr[{pstr_desc=Pstr_eval (e,_);_}];_}] ->
         (handle_record records e)::attrs
      | _::_::_ -> failwith "only one s.t attribute accepted"
      | _ -> failwith "bad s.t attribute")
  | _ -> attrs

let such_that_mapper =
  let handle_td _mapper ({ptype_kind; ptype_attributes; _} as td) =
    let satisfying_attribute = unsugarize ptype_kind ptype_attributes in
    {td with ptype_attributes = satisfying_attribute}
  in
  {default_mapper with type_declaration = handle_td}
