open Migrate_parsetree
open Ast_410
open Parsetree
open Ast_mapper
open Ast_helper
open Helper

let ocaml_version = Versions.ocaml_410
module Conv = Convert (OCaml_410) (OCaml_current)

(* Testify generates an empty (Test.t list ref) at the beginning of
   the ast, and each time a fully annotated function whose return type
   was attached a satisfying predicate, it adds the to the list the
   corresponding test. *)
let test_id = "__Testify__tests"
let test_exp = exp_id test_id

(* ast for : let __Testify__tests = ref [] *)
let declare_test_suite =
  let ref_empty = apply_nolbl_s "ref" [empty_list_exp] in
  str_nonrec [vb_s test_id ref_empty]

(* given x, generates the ast for :
   let _ = __Testify__tests :=  x::!__Testify__tests *)
let add new_test =
  assign [test_exp; cons_exp new_test (bang [test_exp])] |> Str.eval

(* ast for : let _ = QCheck_base_runner.run_tests_main !__Testify__tests *)
let run =
  apply_lab_nolab_s "QCheck_base_runner.run_tests"
    ["colors", true_] [bang [test_exp]] |> Str.eval

(* number of generation per test *)
let count = ref 1000

(* QCheck test for constants *)
let test_constant name f =
  let open Exp in
  let f = fun_ Nolabel None (Pat.any ()) (apply_nolbl f [exp_id name]) in
  let labelled = ["count", int_exp 1; "name", string_exp name] in
  let not_labelled = [exp_id "QCheck.unit"; f] in
  apply_lab_nolab (exp_id "QCheck.Test.make") labelled not_labelled |> add

(* generation of QCheck test *)
let test name args =
  let lab = ["count", int_exp (!count);"name", string_exp name] in
  apply_lab_nolab (exp_id "QCheck.Test.make") lab args |> add

(* builds an input from a list of generators and apply to it the
   function funname *)
let generate inputs fn testname satisfy =
  let get_name =
    let cpt = ref 0 in
    fun () -> incr cpt; "x"^(string_of_int !cpt)
  in
  let rec aux gen pat args = function
    | [] -> gen,pat,List.rev args
    | h::tl ->
       let gen = apply_nolbl_s "QCheck.Gen.pair" [gen; h] in
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
     let f = exp_id fn in
     let f = Exp.fun_ Nolabel None pat (apply_nolbl satisfy [apply_nolbl f args]) in
     let testname = Format.asprintf "the return value of %s violates \
                                     the predicate%a\nfor the \
                                     following input"
                      testname
                      Pprintast.expression (Conv.copy_expression satisfy)
     in
     test testname [apply_nolbl_s "QCheck.make" [gen];f]
  | [] -> assert false


(* Utilities for state rewritting *)
(**********************************)

(* map for type identifier *)
module Types = Map.Make(struct type t = Longident.t let compare = compare end)

let add_prop t_id : expression -> expression Types.t -> expression Types.t =
  Types.add (Longident.Lident t_id)

(* main type, for rewritting states *)
type rewritting_state = {
    generators : expression Types.t;
    properties : expression Types.t;
    printers   : expression Types.t;
  }

let register_printer rs lid p =
  {rs with printers = Types.add lid p rs.printers}

let register_generator rs lid g =
  {rs with generators = Types.add lid g rs.generators}

(* Given a rewritting state [rs] and and a type [t], search for the
   generator associated to [t] in [rs]. Returns a parsetree expression
   corresponding to a Gen.t option. *)
let rec get_generator rs (typ:core_type) =
  match typ.ptyp_desc with
  | Ptyp_constr ({txt;_},[]) -> Types.find_opt txt rs.generators
  |	Ptyp_poly ([],ct)   -> get_generator rs ct
  | Ptyp_tuple [ct1;ct2] ->
     (match get_generator rs ct1,  get_generator rs ct2 with
      | Some t1,Some t2 -> Some (apply_nolbl_s "QCheck.Gen.pair" [t1;t2])
      | _ -> None)
  | _ -> None

(* Given a rewritting state [rs] and and a type [t], search for the
   printer associated to [t] in [rs]. Returns a parsetree expression
   corresponding to a printer option. *)
let rec get_printer rs (typ:core_type) =
  match typ.ptyp_desc with
  | Ptyp_constr ({txt;_},[]) -> Types.find_opt txt rs.generators
  |	Ptyp_poly ([],ct)   -> get_printer rs ct
  | Ptyp_tuple [ct1;ct2] ->
     (match get_printer rs ct1,  get_printer rs ct2 with
      | Some t1,Some t2 -> Some (apply_nolbl_s "QCheck.Print.pair" [t1;t2])
      | _ -> None)
  | _ -> None

(* gets the property attached to the type [t] in [rs] (or None) *)
let rec get_property (t:core_type) (rs:rewritting_state) : expression option =
  match t.ptyp_desc with
  | Ptyp_constr ({txt;_},[]) -> Types.find_opt txt rs.properties
  |	Ptyp_poly ([],ct)   -> get_property ct rs
  | _ -> None

(* initial rewritting state, with a few generators/printers by default *)
let initial_rs =
  let add_id (t_id:string) (id:string) =
    Types.add (Longident.Lident t_id) (exp_id id)
  in
  (* TODO: add entries for int32, int64, nativeint, string, bytes,
     aliases Mod.t *)
  (* TODO: add entries for parametric types ref, list, array, option, lazy_t *)
  let generators =
    Types.empty
    |> add_id "unit"  "QCheck.Gen.unit"
    |> add_id "bool"  "QCheck.Gen.bool"
    |> add_id "char"  "QCheck.Gen.char"
    |> add_id "int"   "QCheck.Gen.int"
    |> add_id "float" "QCheck.Gen.float"
  in
  (* todo fix compatibility *)
  let printers =
    Types.empty
    |> add_id "int" "Int.to_string"
    |> add_id "float" "Float.to_string"
  in
  {generators; printers; properties=Types.empty}

let derive s td =
  match td.ptype_manifest with
  | None -> s
  | Some m ->
     let id = lid td.ptype_name.txt in
     let s =
       Option.fold ~none:s ~some:(register_generator s id) (get_generator s m)
     in
     Option.fold ~none:s ~some:(register_printer s id) (get_printer s m)

(* update the rewritting state according to a type declaration *)
let declare_type state td =
  let state = derive state td in
  match td.ptype_manifest with
  | Some {ptyp_attributes;_} ->
     (match List.filter (fun a -> a.attr_name.txt = "satisfying") ptyp_attributes with
      | [] -> state
      | _::_::_ -> failwith "only one satisfying attribute accepted"
      | [{attr_payload=PStr [{pstr_desc=Pstr_eval (e,_);_}];_}] ->
         let state =
           match Option.bind td.ptype_manifest (get_generator state) with
           | None -> state
           | Some g ->
              let g = apply_lab_nolab_s "QCheck.find_example"
                        ["f", e; "count", int_exp (!count)] [g] in
              register_generator state (lid td.ptype_name.txt) g
         in
         {state with properties = add_prop td.ptype_name.txt e state.properties}
      | _ -> failwith "bad satisfying attribute")
  | None -> state

(* annotation handling *)
(***********************)
let check_gen state pvb =
  (match List.filter (fun a -> a.attr_name.txt="gen") pvb.pvb_attributes with
   | [] -> state
   | _::_::_ -> failwith "only one gen attribute accepted"
   | [{attr_payload=PStr [{pstr_desc=Pstr_eval ({pexp_desc=Pexp_ident l;_},_);_}];_}] ->
      {state with generators = Types.add l.txt pvb.pvb_expr state.generators}
   | _ -> failwith "bad gen attribute"
  )

let check_print state pvb =
  (match List.filter (fun a -> a.attr_name.txt="print") pvb.pvb_attributes with
   | [] -> state
   | _::_::_ -> failwith "only one print attribute accepted"
   | [{attr_payload=PStr [{pstr_desc=Pstr_eval ({pexp_desc=Pexp_ident l;_},_);_}];_}] ->
      {state with printers = Types.add l.txt pvb.pvb_expr state.printers}
   | _ -> failwith "bad print attribute")

let get_info get state e =
  let helper state pat =
    match pat.ppat_desc with
    | Ppat_constraint (_,ct) -> (get state ct)
    | _ -> None
  in
  let rec aux state res = function
    | Pexp_fun(Nolabel,None,pat,exp) ->
       (match helper state pat with
        | Some g -> aux state (g::res) exp.pexp_desc
        | _ -> raise Exit)
    | Pexp_constraint (_,ct) -> state,(List.rev res),ct
    | _ -> raise Exit
  in
  try Some (aux state [] e)
  with Exit -> None

(* returns the generators associated to a function's arguments *)
let fun_decl_to_gen = get_info get_generator

(* returns the printer associated to a function's arguments *)
let fun_decl_to_print = get_info get_printer

(* compute a list of structure item to be added to the AST.
   handles:
   - annotated constants
   - fully annotated functions *)
let check_tests state = function
    (* let constant:typ = val*)
  | {pvb_pat={ppat_desc=Ppat_constraint({ppat_desc=Ppat_var({txt;_});_},typ);_};_} ->
     get_property typ state
     |> Option.fold ~none:[] ~some:(fun p -> [test_constant txt p])
    (* let fn (arg1:typ1) (arg2:typ2) ... : return_typ = body *)
  | {pvb_pat={ppat_desc=Ppat_var({txt;_});_}; pvb_expr;pvb_loc;_} ->
     (match fun_decl_to_gen state pvb_expr.pexp_desc with
      | None -> []
      | Some (_,args,ct) ->
         let name = Format.asprintf "'%s' in %a" txt Location.print_loc pvb_loc in
         get_property ct state
         |> Option.fold ~none:[] ~some: (fun p -> [generate args txt name p]))
  | _ -> []

(* actual mapper *)
let testify_mapper =
  let handle_str mapper str =
    let rec aux state res = function
      | [] -> List.rev (run::res)
      | ({pstr_desc=Pstr_type(_,[t]);_} as h)::tl ->
         aux (declare_type state t) (h::res) tl
      | ({pstr_desc=Pstr_value(_,[pvb]); _} as h)::tl ->
         let tests = check_tests state pvb in
         let state = check_gen state pvb in
         let state = check_print state pvb in
         let h' = mapper.structure_item mapper h in
         aux state (tests@(h'::res)) tl
      | h::tl -> aux state (h::res) tl
    in
    aux initial_rs [declare_test_suite] (str)
  in
  {default_mapper with structure = handle_str}

(* registering the mapper *)
let () =
  let open Migrate_parsetree in
  Driver.register ~name:"ppx_testify" ~args:[]
    Versions.ocaml_410 (fun _config _cookies -> testify_mapper)
