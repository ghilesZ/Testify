open Migrate_parsetree
open Ast_408
open Parsetree
open Ast_mapper
open Ast_helper
open Location

let ocaml_version = Versions.ocaml_408
module Convert_to_current = Convert (OCaml_408) (OCaml_current)

(* given a function name [fn], builds the identifier [fn] *)
let id ?loc:(loc=none) fname =
  Exp.ident ~loc {txt = Lident fname; loc}

module Types = Map.Make(struct type t = core_type_desc let compare = compare end)

type rewritting_state = {
    filename     : string;
    declarations : type_declaration Types.t;
    generators   : expression Types.t;
    dependant    : expression Types.t
  }

(* if no generator is attached to the type, we search for its
   declaration and derive automatically a generator from it. TODO: if
   the declaration was itself a dependant type, adapt generator *)
let rec get_generator rs typ =
  match Types.find_opt typ rs.generators with
  | None -> derive rs typ
  | x -> rs,x
and derive rs typ =
  match Types.find_opt typ rs.declarations with
  | None -> rs,None
  | Some {ptype_params=[];
          ptype_cstrs=[];
          ptype_manifest=Some {ptyp_desc;_};_} ->
     let rs,gen = get_generator rs ptyp_desc in
     (match gen with
     | Some gen as x -> {rs with generators=Types.add typ gen rs.generators},x
     | None -> rs,gen)
  | _ -> rs,None

let add_gen t_id gen_id =
  Types.add (Ptyp_constr((mkloc (Longident.Lident t_id) none),[]))
    (id gen_id)

let add_prop t_id loc : expression -> expression Types.t -> expression Types.t =
  Types.add (Ptyp_constr((mkloc (Longident.Lident t_id) loc),[]))

let initial_rs =
  let generators =
    Types.empty
    |> add_gen "int"   "QCheck.int"
    |> add_gen "float" "QCheck.float"
    |> add_gen "bool"  "QCheck.bool"
  in
  {filename=""; declarations=Types.empty; generators; dependant=Types.empty}

let gather state td =
  match td.ptype_manifest with
  | Some {ptyp_attributes;_} ->
     (match List.filter (fun a -> a.attr_name.txt = "satisfying") ptyp_attributes with
      | [] -> state
      | _::_::_ -> failwith "only one satisfying attribute accepted"
      | [{attr_payload=PStr [{pstr_desc=Pstr_eval (e,_);_}];_}] ->
         {state with dependant = add_prop td.ptype_name.txt td.ptype_loc e state.dependant}
      | _ -> failwith "bad satisfying attribute")
  | None -> state

let testify_mapper =
  let handle_str mapper =
    let rec aux state res = function
      | [] -> List.rev res
      | ({pstr_desc= Pstr_type(_,[td]);_} as h)::tl ->
         let s' = gather state td in
         aux s' (h::res) tl
      (* | {pstr_desc=
       *      Pstr_value(_,[
       *            {pvb_pat={ppat_desc=Ppat_constraint(
       *                                    {ppat_desc=Ppat_var({txt=funname;_});_},
       *                                    typ);
       *                      ppat_loc;_}
       *            ;_}]);pstr_loc} :: tl ->
       *    assert false *)
      | h::tl ->
         let h' = mapper.structure_item mapper h in
         aux state (h'::res) tl
    in
    aux initial_rs []
  in
  {default_mapper with structure = handle_str}

let () =
  let open Migrate_parsetree in
  Driver.register ~name:"ppx_testify" ~args:[]
    Versions.ocaml_408 (fun _config _cookies -> testify_mapper)
