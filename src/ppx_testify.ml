open Migrate_parsetree
open Ast_408
open Parsetree
open Ast_mapper
open Ast_helper
open Asttypes

let ocaml_version = Versions.ocaml_408
module Conv = Convert (OCaml_408) (OCaml_current)

(* Helpers for ast building *)
(****************************)

(* same as mkloc but with optional argument; default is Location.none*)
let none_loc ?loc:(loc=Location.none) s =
  Location.mkloc s loc

(* builds a Longident.t Location.t for a string *)
let lid ?loc:(loc=Location.none) id =
  none_loc ~loc (Longident.parse id)

(* given a string [name], builds the identifier [name] *)
let exp_id ?loc:(loc=Location.none) name =
  lid name |> Exp.ident ~loc

let apply_nolbl f args =
  Exp.apply f (List.map (fun a -> Nolabel,a) args)

let test_suite_name = "__Testify__tests"
let test_suite_exp = exp_id test_suite_name

let add new_test =
  let added =
    let tuple = Exp.tuple [new_test; apply_nolbl (exp_id "!") [test_suite_exp]] in
    Exp.construct (lid "::") (Some tuple)
  in
  apply_nolbl (exp_id ":=") [test_suite_exp; added] |> Str.eval

let declare_test_suite =
  let ref_empty = apply_nolbl (exp_id "ref") [Exp.construct (lid "[]") None] in
  Str.value Nonrecursive [Vb.mk (Pat.var (none_loc test_suite_name)) ref_empty]

let run =
  apply_nolbl (exp_id "QCheck_base_runner.run_tests_main")
    [apply_nolbl (exp_id "!") [test_suite_exp]] |> Str.eval

(* number of generation per test *)
let count = ref 1000

(* let _ = assert (f a) *)
let testify_call f a =
  Str.eval (Exp.(assert_(apply f [Nolabel,a])))

(* generation of QCheck test *)
let test name args =
  let open Exp in
  let args =
    [Labelled "count", Exp.constant (Const.int (!count));
     Labelled "name", Exp.constant (Const.string name)]
    @(List.map (fun e -> Nolabel,e) args)
  in
  open_
    (Opn.mk (Mod.ident (lid "QCheck")))
    (apply (exp_id "Test.make") args)
  |> add

(* building an input from a list of generators and apply to it the
   function funname *)
let generate inputs funname satisfy =
  let get_name =
    let cpt = ref 0 in
    fun () -> incr cpt; "x"^(string_of_int !cpt)
  in
  let rec aux gen pat args = function
    | [] -> gen,pat,List.rev args
    | h::tl ->
       let gen = apply_nolbl (exp_id "QCheck.pair") [gen; h] in
       let name = get_name () in
       let pat = Pat.tuple [pat; Pat.var (none_loc name)] in
       let args = (exp_id name)::args in
       aux gen pat args tl
  in
  match inputs with
  | h::tl ->
     let name = get_name () in
     let pat = Pat.var (none_loc name) in
     let gen,pat,args = aux h pat [exp_id name] tl in
     let f = exp_id funname in
     let f = Exp.fun_ Nolabel None pat (apply_nolbl satisfy [apply_nolbl f args]) in
     let testname = Format.asprintf "Test : %s according to %a" funname
                      Pprintast.expression (Conv.copy_expression satisfy) in
     test testname [gen;f]
  | [] -> assert false


(* Utilities for state rewritting *)
(**********************************)

(* map for type identifier *)
module Types = Map.Make(struct type t = Longident.t let compare = compare end)

(* [add_gen t g map] registers [g] as a generator for the type [t] in [map]*)
let add_gen (t_id:string) (gen_id:string) =
  Types.add (Longident.Lident t_id) (exp_id gen_id)

let add_prop t_id : expression -> expression Types.t -> expression Types.t =
  Types.add (Longident.Lident t_id)

(* sets for type declarations *)
module Decl = Set.Make(struct type t = type_declaration let compare = compare end)

(* search for the declaration of the type with identifier [lid]*)
let find_decl lid decl =
  Decl.find_first_opt (fun td ->
      (Longident.parse td.ptype_name.txt) = lid
    ) decl

(* main type, for rewritting states *)
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

(* Checks if a property is attached to the type [t] in [rs] *)
let rec get_property (t:typ) (rs:rewritting_state) : expression option =
  match t.ptyp_desc with
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

(* returns the generator associated to a function's argument *)
let extract_gen state pat =
  match pat.ppat_desc with
  | Ppat_constraint (_,ct) -> (get_generator state ct)
  | _ -> state,None

let fun_decl_to_gen state e =
  let rec aux state res = function
    | Pexp_fun(Nolabel,None,pat,exp) ->
       (match extract_gen state pat with
        | s, Some g -> aux s (g::res) exp.pexp_desc
        | _ -> raise Exit)
    | Pexp_constraint (_,ct) -> state,(List.rev res),ct
    | _ -> raise Exit
  in
  try Some (aux state [] e)
  with Exit -> None

let testify_mapper =
  let update state = function
    | Pstr_type(_,[td]) -> declare_type state td, []
    | Pstr_value(_,[{pvb_pat={ppat_desc=Ppat_constraint(
                                            {ppat_desc=Ppat_var({txt;_});_},
                                            typ);
                              _};_}]) ->
       (match get_property typ state with
        | None -> state,[]
        | Some p -> state, [testify_call p (exp_id txt)])
    | Pstr_value(_,[
            {pvb_pat={ppat_desc=Ppat_var({txt;_});_}; pvb_expr;_}]) ->
       (match fun_decl_to_gen state pvb_expr.pexp_desc with
        | None -> state,[]
        | Some (s,args,ct) ->
           (match get_property ct state with
            | None -> s,[]
            | Some p -> s, [generate args txt p])
       )

    | _ -> state,[]
  in

  let handle_str mapper =
    let rec aux state res = function
      | [] -> List.rev (run::res)
      | h::tl ->
         let state,tests = update state h.pstr_desc in
         let h' = mapper.structure_item mapper h in
         aux state (tests@(h'::res)) tl
    in
    aux initial_rs [declare_test_suite]
  in
  {default_mapper with structure = handle_str}

let () =
  let open Migrate_parsetree in
  Driver.register ~name:"ppx_testify" ~args:[]
    Versions.ocaml_408 (fun _config _cookies -> testify_mapper)
