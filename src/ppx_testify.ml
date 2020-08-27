open Migrate_parsetree
open Ast_408
open Parsetree
open Ast_mapper
open Ast_helper
open Location

let ocaml_version = Versions.ocaml_408
module Conv = Convert (OCaml_408) (OCaml_current)

(* PPX helpers *)

(* given a string [name], builds the identifier [name] *)
let id ?loc:(loc=none) name =
  Exp.ident ~loc {txt = Lident name; loc}

(* let _ = assert (f a) *)
let testify_call0 f a =
  Str.eval (Exp.(assert_(apply f [Nolabel,a])))

module Types = Map.Make(struct type t = Longident.t let compare = compare end)
module Decl = Set.Make(struct type t = type_declaration let compare = compare end)

let add_gen t_id gen_id =
  Types.add (Longident.Lident t_id) (id gen_id)

let add_prop t_id : expression -> expression Types.t -> expression Types.t =
  Types.add (Longident.Lident t_id)

(* search for the declaration of the type with identifier [lid]*)
let find_decl lid decl =
  Decl.find_first_opt (fun td ->
      (Longident.parse td.ptype_name.txt) = lid
    ) decl

type rewritting_state = {
    filename     : string;
    declarations : Decl.t;
    generators   : expression Types.t;
    properties   : expression Types.t
  }

(* Given a rewritting state [rs] and and a type [t], search for the
   generator (currently) associated to [t] in [rs]. If no generator is
   attached to [t], we search for its declaration and try to derive
   automatically a generator from it. Returns the rewritting state
   updated with potentially new generators, and agenerator option.
   TODO: if the declaration was itself a dependant type, adapt
   generator *)
let rec get_generator rs (typ:core_type) =
  match typ.ptyp_desc with
  | Ptyp_constr ({txt;_},[]) ->
     (try Types.find txt rs.generators |> add_to_rs rs txt
      with Not_found ->
            let decl = find_decl txt rs.declarations in
            match decl with
            | Some {ptype_manifest = Some t;_} -> get_generator rs t
            | _ -> rs,None)
  |	Ptyp_poly ([],ct)   -> get_generator rs ct
  | _ -> rs,None
and add_to_rs rs t g =
  {rs with generators = Types.add t g rs.generators},Some g

(* Checks if a property is attached to the type [ct] in [rs] *)
let rec get_property ct rs : expression option =
  match ct.ptyp_desc with
  | Ptyp_constr ({txt;_},[]) -> Types.find_opt txt rs.properties
  |	Ptyp_poly ([],ct)   -> get_property ct rs
  | _ -> None

(* initial rewritting state, with a few generators by default *)
let initial_rs =
  let generators =
    Types.empty
    |> add_gen "int"   "QCheck.int"
    |> add_gen "float" "QCheck.float"
    |> add_gen "bool"  "QCheck.bool"
  in
  {filename=""; declarations=Decl.empty; generators; properties=Types.empty}

(* update the rewritting state according to a type declaration *)
let declare_type state td =
  match td.ptype_manifest with
  | Some {ptyp_attributes;_} ->
     (match List.filter (fun a -> a.attr_name.txt = "satisfying") ptyp_attributes with
      | [] -> state
      | _::_::_ -> failwith "only one satisfying attribute accepted"
      | [{attr_payload=PStr [{pstr_desc=Pstr_eval (e,_);_}];_}] ->
         (* Format.printf "adding %s to the list of dependant types w.r.t %a\n"
          *   td.ptype_name.txt
          *   Pprintast.expression (Conv.copy_expression e); *)
         {state with
           properties = add_prop td.ptype_name.txt e state.properties;
           declarations = Decl.add td state.declarations}
      | _ -> failwith "bad satisfying attribute")
  | None -> state

let testify_mapper =
  let handle_str mapper =
    let rec aux state res = function
      | [] -> List.rev res
      | ({pstr_desc=Pstr_type(_,[td]);_} as h)::tl ->
         aux(declare_type state td) (h::res) tl
      | ({pstr_desc=
            Pstr_value(_,[
                  {pvb_pat={ppat_desc=Ppat_constraint(
                                          {ppat_desc=Ppat_var({txt;_});_},
                                          typ);
                            _};_}]);_} as h) :: tl ->
         (* if a property is attached to the type, we generate the corresponding test *)
         (match get_property typ state with
          | None -> aux state (h::res) tl
          | Some p -> aux state ((testify_call0 p (id txt))::h::res) tl)
      (* let s',g = get_generator state typ in
       * let typ' = Conv.copy_core_type typ in
       * (match g with
       * | None -> Format.printf "no generator for type %a\n" Pprintast.core_type typ'
       * | Some _ -> Format.printf "generator found for type %a\n" Pprintast.core_type typ'); *)
      | h::tl -> let h' = mapper.structure_item mapper h in aux state (h'::res) tl
    in
    aux initial_rs []
  in
  {default_mapper with structure = handle_str}

let () =
  let open Migrate_parsetree in
  Driver.register ~name:"ppx_testify" ~args:[]
    Versions.ocaml_408 (fun _config _cookies -> testify_mapper)
