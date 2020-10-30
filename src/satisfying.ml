open Migrate_parsetree
open Ast_410
open Parsetree
open Ast_mapper
open Ast_helper
open Helper

let ocaml_version = Versions.ocaml_410
module Conv = Convert (OCaml_410) (OCaml_current)

let add new_test =
  apply_nolbl_s "Testify_runtime.add_test" [new_test] |> Str.eval

let run =
  apply_nolbl_s "Testify_runtime.run_test" [unit] |> Str.eval

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

(* same as [pp], but in bold blue] *)
  let bold_blue x =
    Format.asprintf "\x1b[34;1m%s\x1b[0m" x

(* same as [pp], but in blue *)
  let blue x =
    Format.asprintf "\x1b[36m%s\x1b[0m" x

(* builds an input from a list of generators and printers and apply
   to it the function funname *)
let generate inputs fn testname satisfy =
  let rec aux gen print pat args = function
    | [] -> gen,print,pat,List.rev args
    | (g,p)::tl ->
       let print = apply_nolbl_s "QCheck.Print.pair" [print; p] in
       let gen = apply_nolbl_s "QCheck.Gen.pair" [gen; g] in
       let name = get_name () in
       let pat = Pat.tuple [pat; pat_s name] in
       let args = (exp_id name)::args in
       aux gen print pat args tl
  in
  match inputs with
  | (g,p)::tl ->
     let name = get_name () in
     let pat = pat_s name in
     let gen,print,pat,args = aux g p pat [exp_id name] tl in
     let f = exp_id fn in
     let f = Exp.fun_ Nolabel None pat (apply_nolbl satisfy [apply_nolbl f args]) in
     let testname = Format.asprintf "the return value of %s violates \
                                     the predicate%a\nfor the \
                                     following input:\n"
                      testname
                      Pprintast.expression (Conv.copy_expression satisfy)
     in
     test testname [apply_lab_nolab_s "QCheck.make" ["print",print] [gen];f]
  | [] -> assert false

(* Utilities for state rewritting *)
(**********************************)

(* main type, for rewritting state. keeps tracks of :
  - test properties attached to a type.
  - current generators and printers *)
type rewritting_state = {
    properties : expression Types.t;
    generators : expression Types.t;
    printers   : expression Types.t;
  }

let register_printer rs lid p =
  {rs with printers = Types.add lid p rs.printers}

let register_generator rs lid g =
  {rs with generators = Types.add lid g rs.generators}

let get_gen_core_type rs =
  let rec aux ct =
    match ct.ptyp_desc with
    | Ptyp_constr ({txt;_},[]) -> Types.find_opt txt rs.generators
    |	Ptyp_poly ([],ct)   -> aux ct
    | Ptyp_tuple tup ->
       let gens = List.map aux tup in
       (try
          List.map (fun g -> apply_nolbl (Option.get g) [exp_id "x"]) gens
          |> Exp.tuple
          |> Exp.fun_ Nolabel None (pat_s "x")
          |> Option.some
        with Invalid_argument _ -> None)
    | _ -> None
  in aux

let get_printer_core_type rs =
  let rec aux ct =
    match ct.ptyp_desc with
    | Ptyp_constr ({txt;_},[]) -> Types.find_opt txt rs.printers
    |	Ptyp_poly ([],ct)   -> aux ct
    | Ptyp_tuple tup ->
       let prints = List.map aux tup in
       (try
          let np p =
            let n = get_name() in
            apply_nolbl (Option.get p) [exp_id n], pat_s n
          in
          let names,pats = List.split (List.map np prints) in
          let b = string_concat ~sep:", " names in
          let b' = string_concat [string_exp "("; b; string_exp ")"] in
          Some (Exp.fun_ Nolabel None (Pat.tuple pats) b')
        with Invalid_argument _ -> None)
    | _ -> None
  in aux

(* Given a rewritting state [rs] and and a type [t], search for the
   generator associated to [t] in [rs]. Returns a Parsetree.expression
   (corresponding to a Gen.t) option. *)
let get_generator rs t =
  match t.ptype_kind with
  |	Ptype_abstract ->
     (match t.ptype_manifest with
     | None -> None
     | Some m -> get_gen_core_type rs m)
  |	Ptype_variant _ -> None
  |	Ptype_record labs ->
     (try
        let handle_field f =
          let gen = get_gen_core_type rs f.pld_type |> Option.get in
          lid_loc f.pld_name.txt, apply_nolbl gen [exp_id "rs"]
        in
        let app = Exp.record (List.map handle_field labs) None in
        Some (Exp.fun_ Nolabel None (pat_s "rs") app)
      with Invalid_argument _ -> None
     )
  |	Ptype_open -> None

(* Given a rewritting state [rs] and and a type [t], search for the
   printer associated to [t] in [rs]. Returns a Parsetree.expression
   (corresponding to a printer) option. *)
let get_printer rs t =
  match t.ptype_kind with
  |	Ptype_abstract ->
     (match t.ptype_manifest with
     | None -> None
     | Some m -> get_printer_core_type rs m)
  |	Ptype_variant _ -> None
  |	Ptype_record labs ->
     (try
        let handle_field f =
          let print = get_printer_core_type rs f.pld_type |> Option.get in
          let field = apply_nolbl print [exp_id f.pld_name.txt] in
          let field_name = string_exp f.pld_name.txt in
          string_concat ~sep:"=" [field_name;field]
        in
        let to_s f = f.pld_name.txt in
        let app = string_concat ~sep:"; " (List.map handle_field labs) in
        let app = string_concat [string_exp "{"; app; string_exp "}"] in
        let pat = List.map (fun l -> lid_loc (to_s l), pat_s (to_s l)) labs in
        Some (Exp.fun_ Nolabel None (Pat.record pat Closed) app)
      with Invalid_argument _ -> None
     )  |	Ptype_open -> None

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
  let printers =
    Types.empty
    |> add_id "unit"  "QCheck.Print.unit"
    |> add_id "bool"  "string_of_bool"
    |> add_id "char"  "string_of_char"
    |> add_id "int"   "string_of_int"
    |> add_id "float" "string_of_float"
  in
  {generators; printers; properties=Types.empty}

let derive s td =
  let id = lid td.ptype_name.txt in
  let s =
    Option.fold ~none:s ~some:(register_generator s id) (get_generator s td)
  in
  Option.fold ~none:s ~some:(register_printer s id) (get_printer s td)

(* update the rewritting state according to a type declaration *)
let declare_type state td =
  let state = derive state td in
  (match List.filter (fun a -> a.attr_name.txt = "satisfying") td.ptype_attributes with
   | [] -> state
   | [{attr_payload=PStr[{pstr_desc=Pstr_eval (e,_);_}];_}] ->
      let state =
        match get_generator state td with
        | None -> state
        | Some g ->
           let g = apply_lab_nolab_s "QCheck.find_example"
                     ["f", e; "count", int_exp (!count)] [g]
           in register_generator state (lid td.ptype_name.txt) g
      in
      {state with properties = add_s td.ptype_name.txt e state.properties}
   | _::_::_ -> failwith "only one satisfying attribute accepted"
   | _ -> failwith "bad satisfying attribute")

(* annotation handling *)
(***********************)

let check_gen state pvb =
  (match List.filter (fun a -> a.attr_name.txt="gen") pvb.pvb_attributes with
   | [] -> state
   | _::_::_ -> failwith "only one gen attribute accepted"
   | [{attr_payload=PStr [{pstr_desc=Pstr_eval ({pexp_desc=Pexp_ident l;_},_);_}];_}] ->
      {state with generators = Types.add l.txt pvb.pvb_expr state.generators}
   | _ -> failwith "bad gen attribute")

let check_print state pvb =
  (match List.filter (fun a -> a.attr_name.txt="print") pvb.pvb_attributes with
   | [] -> state
   | _::_::_ -> failwith "only one print attribute accepted"
   | [{attr_payload=PStr [{pstr_desc=Pstr_eval ({pexp_desc=Pexp_ident l;_},_);_}];_}] ->
      {state with printers = Types.add l.txt pvb.pvb_expr state.printers}
   | _ -> failwith "bad print attribute")

let get_infos state e =
  let helper state pat =
    match pat.ppat_desc with
    | Ppat_constraint (_,ct) ->
       (get_gen_core_type state ct),(get_printer_core_type state ct)
    | _ -> None,None
  in
  let rec aux state res = function
    | Pexp_fun(Nolabel,None,pat,exp) ->
       (match helper state pat with
        | Some g,Some p -> aux state ((g,p)::res) exp.pexp_desc
        | _ -> raise Exit)
    | Pexp_constraint (_,ct) -> state,(List.rev res),ct
    | _ -> raise Exit
  in
  try Some (aux state [] e)
  with Exit -> None

(* compute a list of tests to be added to the AST.
   handles:
   - explicitly typed constants
   - (fully) explicitly typed functions *)
let check_tests state = function
  (* let constant:typ = val*)
  | {pvb_pat={ppat_desc=Ppat_constraint({ppat_desc=Ppat_var({txt;_});_},typ);_};_} ->
     get_property typ state
     |> Option.fold ~none:[] ~some:(fun p -> [test_constant txt p])
  (* let fn (arg1:typ1) (arg2:typ2) ... : return_typ = body *)
  | {pvb_pat={ppat_desc=Ppat_var({txt;_});_};pvb_expr;pvb_loc;_} ->
     (match get_infos state pvb_expr.pexp_desc with
      | None -> []
      | Some (_,args,ct) ->
         let loc = Format.asprintf "%a" Location.print_loc pvb_loc in
         let name = Format.asprintf "%s in %s" (bold_blue txt) (blue loc) in
         get_property ct state
         |> Option.fold ~none:[] ~some: (fun p -> [generate args txt name p]))
  | _ -> []

(* actual mapper *)
let mapper =
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
    aux initial_rs [] (str)
  in
  {default_mapper with structure = handle_str}
