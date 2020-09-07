open Migrate_parsetree
open Ast_408
open Parsetree
open Ast_mapper
open Ast_helper
open Helper

let ocaml_version = Versions.ocaml_408
module Conv = Convert (OCaml_408) (OCaml_current)

(* Testify generates an empty (Test.t list ref) at the beginning of
   the ast, and each time a fully annotated function whose return type
   was attached a satisfying predicate, it adds the to the list the
   corresponding test. *)
let test_id = "__Testify__tests"
let test_exp = exp_id test_id

(* ast for : let __Testify__tests = ref [] *)
let declare_test_suite =
  let ref_empty = apply_nolbl_s "ref" [Exp.construct (lid "[]") None] in
  str_nonrec [Vb.mk (Pat.var (none_loc test_id)) ref_empty]

(* given x, generates the ast for :
   let _ = __Testify__tests :=  x::!__Testify__tests *)
let add new_test =
  let added =
    let tuple = Exp.tuple [new_test; bang [test_exp]] in
    Exp.construct (lid "::") (Some tuple)
  in
  assign [test_exp; added] |> Str.eval

(* ast for : let _ = QCheck_base_runner.run_tests_main !__Testify__tests *)
let run =
  apply_lab_nolab_s "QCheck_base_runner.run_tests"
    ["colors", true_] [bang [test_exp]] |> Str.eval

(* number of generation per test *)
let count = ref 1000

(* let _ = assert (f a) *)
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
                                     the predicate%a\nfor some input" testname
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
    generators   : expression Types.t;
    properties   : expression Types.t
  }

(* Given a rewritting state [rs] and and a type [t], search for the
   generator associated to [t] in [rs]. Returns a Gen.t option. *)
let rec get_generator rs (typ:core_type) =
  match typ.ptyp_desc with
  | Ptyp_constr ({txt;_},[]) -> Types.find_opt txt rs.generators
  |	Ptyp_poly ([],ct)   -> get_generator rs ct
  | Ptyp_tuple [ct1;ct2] ->
     (match get_generator rs ct1,  get_generator rs ct2 with
      | Some t1,Some t2 -> Some (apply_nolbl_s "QCheck.Gen.pair" [t1;t2])
      | _ -> None)
  | _ -> None

(* Checks if a property is attached to the type [t] in [rs] *)
let rec get_property (t:typ) (rs:rewritting_state) : expression option =
  match t.ptyp_desc with
  | Ptyp_constr ({txt;_},[]) -> Types.find_opt txt rs.properties
  |	Ptyp_poly ([],ct)   -> get_property ct rs
  | _ -> None

(* initial rewritting state, with a few generators by default *)
let initial_rs =
  let add_gen (t_id:string) (gen_id:string) =
    Types.add (Longident.Lident t_id) (exp_id gen_id)
  in
  let generators =
    Types.empty
    |> add_gen "unit"  "QCheck.Gen.unit"
    |> add_gen "bool"  "QCheck.Gen.bool"
    |> add_gen "char"  "QCheck.Gen.char"
    |> add_gen "int"   "QCheck.Gen.int"
    |> add_gen "float" "QCheck.Gen.float"
  in
  {generators; properties=Types.empty}

(* update the rewritting state according to a type declaration *)
let declare_type state td =
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
              let g = apply_lab_nolab_s "QCheck.find_example" ["f", e] [g] in
              {state with generators =
                            Types.add (Longident.Lident td.ptype_name.txt)
                              g state.generators}
         in
         {state with properties = add_prop td.ptype_name.txt e state.properties}
      | _ -> failwith "bad satisfying attribute")
  | None -> state

let check_gen state pvb =
  (match List.filter (fun a -> a.attr_name.txt = "gen") pvb.pvb_attributes with
   | [] -> state
   | _::_::_ -> failwith "only one gen attribute accepted"
   | [{attr_payload=PStr [{pstr_desc=Pstr_eval ({pexp_desc=Pexp_ident l;_},_);_}];_}] ->
      {state with generators = Types.add l.txt pvb.pvb_expr state.generators}
   | _ -> failwith "bad gen attribute"
  )

(* returns the generators associated to a function's arguments *)
let fun_decl_to_gen state e =
  let helper state pat =
    match pat.ppat_desc with
    | Ppat_constraint (_,ct) -> (get_generator state ct)
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

(* compute a list of structure item to be added to the AST.
   handles:
   - annotated constants
   - fully annotated functions *)
let check_tests state = function
  | {pvb_pat={ppat_desc=Ppat_constraint({ppat_desc=Ppat_var({txt;_});_},typ);_};_} ->
     get_property typ state
     |> Option.fold ~none:[] ~some:(fun p -> [test_constant txt p])
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
  let handle_str mapper =
    let rec aux state res = function
      | [] -> List.rev (run::res)
      | ({pstr_desc=Pstr_type(_,[t]);_} as h)::tl ->
         aux (declare_type state t) (h::res) tl
      | ({pstr_desc=Pstr_value(_,[pvb]); _} as h)::tl ->
         let state = check_gen state pvb in
         let tests = check_tests state pvb in
         let h' = mapper.structure_item mapper h in
         aux state (tests@(h'::res)) tl
      | h::tl -> aux  state (h::res) tl
    in
    aux initial_rs [declare_test_suite]
  in
  {default_mapper with structure = handle_str}

(* registering the mapper *)
let () =
  let open Migrate_parsetree in
  Driver.register ~name:"ppx_testify" ~args:[]
    Versions.ocaml_408 (fun _config _cookies -> testify_mapper)
