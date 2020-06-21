open Migrate_parsetree
open Ast_408
open Parsetree
open Ast_mapper
open Ast_helper
open Location

let ocaml_version = Versions.ocaml_408
module Convert_to_current = Convert (OCaml_408) (OCaml_current)

(* TODO: change 1000 *)
let count = ref 1000

let string_of_expression (expr: Parsetree.expression) : string =
  let copy = Convert_to_current.copy_expression expr in
  Format.asprintf "%s" (Pprintast.string_of_expression copy)

(* given a function name [fn], builds the identifier [fn] *)
let id ?loc:(loc=none) fname =
  Exp.ident ~loc {txt = Lident fname; loc}

(* given an expression 'e', generates the ast fragment for "let _ = e"*)
let wild_card_declaration loc expr = Str.eval ~loc expr

let testify_call funname testname args =
  let open Asttypes in
    Exp.(apply (id funname) ([
      Labelled "count", constant (Pconst_integer (string_of_int (!count),None));
      Labelled "name", constant (Pconst_string (testname,None));
    ]@(List.map (fun e -> Nolabel,e) args)))

let call funname title gen arg =
  testify_call funname title [gen;arg]

let call2 funname title gen arg1 arg2 =
   testify_call funname title [gen; arg1; arg2]

let call4 funname title gen arg1 arg2 arg3 arg4 =
  testify_call funname title [gen; arg1; arg2; arg3; arg4]

let commut_test loc funname gen : structure_item =
  let fname,_,_ = get_pos_info loc.loc_start in
  let testname = funname^" in file "^fname^" is commutative" in
  let test = call "commut" testname gen (id funname) in
  wild_card_declaration loc test

let assoc_test loc funname gen : structure_item =
  let fname,_,_ = get_pos_info loc.loc_start in
  let testname = funname^" in file "^fname^" is associative" in
  let test = call "assoc" testname gen (id funname) in
  wild_card_declaration loc test

let distrib_test loc funname1 over gen : structure_item =
  let fname,_,_ = get_pos_info loc.loc_start in
  let str = string_of_expression over in
  let testname = funname1^" in file "^fname^"is distributive over "^str in
  let test = call2 "distrib" testname gen (id funname1) over   in
  wild_card_declaration loc test

let over_approx_test loc funname1 over in_g rand_g gen : structure_item =
  let fname,_,_ = get_pos_info loc.loc_start in
  let str = string_of_expression over in
  let testname = funname1^" in file "^fname^" over-approximates "^str in
  let test = call4 "over_approx2" testname gen (id funname1) over in_g rand_g in
  wild_card_declaration loc test

type ppx_state = {
    gen:expression option;
    in_gamma:expression option;
    rand_gamma:expression option;
  }

let get_gen s =
  match s.gen with
  | None  -> failwith "generator not set"
  | Some g -> g

let get_in_gamma s =
  match s.in_gamma with
  | None  -> failwith "in_gamma not set"
  | Some g -> g

let get_rand_gamma s =
  match s.rand_gamma with
  | None  -> failwith "rand_gamma not set"
  | Some g -> g

(* builds the list of tests to be added to the AST *)
let gather_tests state loc funname (attr:attributes) =
    let helper a : string * expression list =
      match a.attr_payload with
      | PStr [] -> a.attr_name.txt,[]
      | PStr [{pstr_desc=Pstr_eval (f,_);_}] -> a.attr_name.txt,[f]
      | _ -> failwith "invalid payload"
    in
    let aux (state,acc) e =
    match e |> helper with
    | "in_gamma",[] -> {state with in_gamma = Some (id funname)},acc
    | "rand_gamma",[] -> {state with rand_gamma = Some (id funname)},acc
    | "gen",[] -> {state with gen = Some (id funname)},acc
    | "gen",[e] -> {state with gen = Some e},acc
    | "commut",[] -> let t = commut_test loc funname (get_gen state) in
                     state,(t::acc)
    | "assoc",[] -> let t = assoc_test loc funname (get_gen state) in
                    state,(t::acc)
    | "distrib",[f] -> let t = distrib_test loc funname f (get_gen state) in
                       state,(t::acc)
    | "over_approx", [f]->
       let t = over_approx_test loc funname
                 f
                 (get_in_gamma state)
                 (get_rand_gamma state)
                 (get_gen state) in
       state,(t::acc)
    | _ -> state,acc
  in
  List.fold_left aux (state,[]) attr

let call_run =
  let unit_lid = Longident.Lident "()" in
  let ghost = Location.none in
  let unit_lid_loc = Location.mkloc unit_lid ghost in
  let unit = Pexp_construct (unit_lid_loc,None) in
  let call = Exp.(apply (id "run") [Nolabel, Exp.mk unit]) in
  Str.mk (Pstr_eval (call,[]))

let testify_mapper =
  let handle_str mapper =
    let rec aux state res = function
      | [] -> List.rev (call_run::res)
      | ({pstr_desc=
            Pstr_value(_,[
                  {pvb_pat={ppat_desc=Ppat_var ({txt=funname;_});ppat_loc=loc;_}
                  ;pvb_attributes=(_::_ as attr);_}]);_} as h)::tl ->
         let state,tests = gather_tests state loc funname attr in
         aux state (tests@(h::res)) tl
      | h::tl ->
         let h' = mapper.structure_item mapper h in
         aux state (h'::res) tl
    in
    aux {gen=None; in_gamma=None;  rand_gamma=None} []
  in
  {default_mapper with structure = handle_str}

let () =
  let open Migrate_parsetree in
  Driver.register ~name:"ppx_testify" ~args:[]
    Versions.ocaml_408 (fun _config _cookies -> testify_mapper)
