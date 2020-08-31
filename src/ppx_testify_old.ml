(* open Migrate_parsetree
 * open Ast_408
 * open Parsetree
 * open Ast_mapper
 * open Ast_helper
 * open Location
 *
 * let ocaml_version = Versions.ocaml_408
 * module Convert_to_current = Convert (OCaml_408) (OCaml_current)
 *
 * (\* TODO: change 1000 *\)
 * let count = ref 1000
 *
 * type rewritting_state = {
 *     filename : string;
 *     gen : expression option;
 *     in_gamma : expression option;
 *     rand_gamma : expression option;
 *     abstract_printer : expression option;
 *     concrete_printer : expression option;
 *   }
 *
 * let initial : rewritting_state = {
 *         filename="";
 *         gen=None;
 *         in_gamma=None;
 *         rand_gamma=None;
 *         abstract_printer=None;
 *         concrete_printer = None
 *       }
 *
 * let get_gen s =
 *   match s.gen with
 *   | None  -> failwith "generator not set"
 *   | Some g -> g
 *
 * let get_in_gamma s =
 *   match s.in_gamma with
 *   | None  -> failwith "in_gamma not set"
 *   | Some g -> g
 *
 * let get_rand_gamma s =
 *   match s.rand_gamma with
 *   | None  -> failwith "rand_gamma not set"
 *   | Some g -> g
 *
 * let get_a_print s =
 *   match s.abstract_printer with
 *   | None  -> failwith "abstract printer not set"
 *   | Some g -> g
 *
 * let get_c_print s =
 *   match s.concrete_printer with
 *   | None  -> failwith "concrete printer not set"
 *   | Some g -> g
 *
 * (\********************************************\)
 * (\* Helpers for building OCaml AST fragments *\)
 * (\********************************************\)
 *
 * let string_of_expression (expr: Parsetree.expression) : string =
 *   let copy = Convert_to_current.copy_expression expr in
 *   Format.asprintf "%s" (Pprintast.string_of_expression copy)
 *
 * let string_to_expression str = Exp.constant (Pconst_string(str,None))
 *
 * (\* given a function name [fn], builds the identifier [fn] *\)
 * let id ?loc:(loc=none) fname =
 *   Exp.ident ~loc {txt = Lident fname; loc}
 *
 * (\* given an expression 'e', generates the ast fragment for "let _ = e"*\)
 * let wild_card_declaration loc expr = Str.eval ~loc expr
 *
 * (\* () *\)
 * let exp_unit =
 *   let unit_lid = Longident.Lident "()" in
 *   let ghost = Location.none in
 *   let unit_lid_loc = Location.mkloc unit_lid ghost in
 *   let unit = Pexp_construct (unit_lid_loc,None) in
 *   Exp.mk unit
 *
 * (\*****************************************\)
 * (\* Helpers for calling testify functions *\)
 * (\*****************************************\)
 * let make_gc gen spawn in_gamma a_print c_print =
 *   let open Asttypes in
 *   Exp.(apply (id "make_gc")
 *          (List.map (fun e -> Nolabel,e)
 *             [gen; spawn; in_gamma; a_print; c_print]))
 *
 * let testify_call funname testname args =
 *   let open Asttypes in
 *     Exp.(apply (id funname) ([
 *       Labelled "count", constant (Pconst_integer (string_of_int (!count),None));
 *       Labelled "name", constant (Pconst_string (testname,None));
 *              ]@(List.map (fun e -> Nolabel,e) args)))
 *
 * let call_run =
 *   let call = Exp.(apply (id "run") [Nolabel, exp_unit]) in
 *   Str.mk (Pstr_eval (call,[]))
 *
 * let call1 funname title gen arg =
 *   testify_call funname title [gen;arg]
 *
 * let call2 funname title gen arg1 arg2 =
 *    testify_call funname title [gen; arg1; arg2]
 *
 * let call4 funname title gen arg1 arg2 arg3 arg4 =
 *   testify_call funname title [gen; arg1; arg2; arg3; arg4]
 *
 * let commut loc funname gen : structure_item =
 *   let file,_,_ = get_pos_info loc.loc_start in
 *   let testname = funname^" in file "^file^" is commutative" in
 *   let test = call1 "commut" testname gen (id funname) in
 *   wild_card_declaration loc test
 *
 * let assoc loc funname gen : structure_item =
 *   let file,_,_ = get_pos_info loc.loc_start in
 *   let testname = funname^" in file "^file^" is associative" in
 *   let test = call1 "assoc" testname gen (id funname) in
 *   wild_card_declaration loc test
 *
 * let distrib loc funname1 over gen : structure_item =
 *   let file,_,_ = get_pos_info loc.loc_start in
 *   let str = string_of_expression over in
 *   let testname = funname1^" in file "^file^"is distributive over "^str in
 *   let test = call2 "distrib" testname gen (id funname1) over   in
 *   wild_card_declaration loc test
 *
 * let over_approx loc funname1 over gen in_g rand_g a_print c_print : structure_item =
 *   let file,_,_ = get_pos_info loc.loc_start in
 *   let str = string_of_expression over in
 *   let gc_exp = make_gc gen rand_g in_g a_print c_print in
 *   let testname = funname1^" in file "^file^" over-approximates "^str in
 *   let test = call4 "over_approx2" testname gc_exp (id funname1) over
 *                (string_to_expression funname1) (string_to_expression str) in
 *   wild_card_declaration loc test
 *
 * (\* builds the list of tests to be added to the AST *\)
 * let gather state loc funname (attr:attributes) =
 *     let helper a : string * expression list =
 *       match a.attr_payload with
 *       | PStr [] -> a.attr_name.txt,[]
 *       | PStr [{pstr_desc=Pstr_eval (f,_);_}] -> a.attr_name.txt,[f]
 *       | _ -> failwith "invalid payload"
 *     in
 *     let id_fun = Some (id funname) in
 *     let aux (state,acc) e =
 *       match e |> helper with
 *       (\* state modification *\)
 *       | "in_gamma",[]         -> {state with in_gamma = id_fun},acc
 *       | "rand_gamma",[]       -> {state with rand_gamma = id_fun},acc
 *       | "gen",[]              -> {state with gen = id_fun},acc
 *       | "abstract_printer",[] -> {state with abstract_printer = id_fun},acc
 *       | "concrete_printer",[] -> {state with concrete_printer = id_fun},acc
 *       (\* test generation *\)
 *       | "commut",[]    -> state,(commut loc funname (get_gen state))::acc
 *       | "assoc",[]    -> state,(assoc loc funname (get_gen state))::acc
 *       | "distrib",[f] -> state,(distrib loc funname f (get_gen state))::acc
 *       | "over_approx", [f]->
 *          let t = over_approx loc funname f (get_gen state) (get_in_gamma state)
 *                    (get_rand_gamma state)
 *                    (get_a_print state)
 *                    (get_c_print state)
 *          in
 *          state,(t::acc)
 *       | _ -> state,acc
 *     in
 *     List.fold_left aux (state,[]) attr
 *
 * let testify_mapper =
 *   let handle_str mapper =
 *     let rec aux state res = function
 *       | [] -> List.rev (call_run::res)
 *       | ({pstr_desc=
 *             Pstr_value(_,[
 *                   {pvb_pat={ppat_desc=Ppat_var ({txt=funname;_});ppat_loc=loc;_}
 *                   ;pvb_attributes=(_::_ as attr);_}]);pstr_loc} as h)::tl ->
 *          let state,tests = gather state loc funname attr in
 *          let filename,_,_= get_pos_info pstr_loc.loc_start in
 *          aux {state with filename} (tests@(h::res)) tl
 *       | h::tl ->
 *          let h' = mapper.structure_item mapper h in
 *          aux state (h'::res) tl
 *     in
 *     aux initial []
 *   in
 *   {default_mapper with structure = handle_str}
 *
 * let () =
 *   let open Migrate_parsetree in
 *   Driver.register ~name:"ppx_testify_old" ~args:[]
 *     Versions.ocaml_408 (fun _config _cookies -> testify_mapper) *)
