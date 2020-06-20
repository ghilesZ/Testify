open Migrate_parsetree.Ast_408
open Parsetree
open Ast_mapper
open Ast_helper
open Location

(* given a function name [fn], builds the identifier [fn] *)
let id fname loc =
  Exp.ident ~loc {txt = Lident fname; loc}

(* given an expression 'e', generates the ast fragment for "let _ = e"*)
let wild_card_declaration expr =
  Pstr_value(Asttypes.Nonrecursive,
             [{pvb_pat={ppat_desc=Ppat_any;
                        ppat_loc=none;
                        ppat_loc_stack=[];
                        ppat_attributes=[]};
               pvb_attributes=[];
               pvb_expr=expr;
               pvb_loc=none
    }])

(* TODO: change 1000 *)
let call loc funname title gen arg =
  Exp.apply ~loc:loc (id funname loc) [
      Labelled "count",Exp.constant (Pconst_integer ("1000",None));
      Labelled "name",Exp.constant (Pconst_string (title,None));
      Nolabel,gen;
      Nolabel,(id arg loc)
    ]

let call2 loc funname title gen arg1 arg2 =
  Exp.apply ~loc:loc (id funname loc) [
      Labelled "count",Exp.constant (Pconst_integer ("1000",None));
      Labelled "name",Exp.constant (Pconst_string (title,None));
      Nolabel,gen;
      Nolabel,(id arg1 loc);
      Nolabel,(id arg2 loc)
    ]

let call4 loc funname title gen arg1 arg2 arg3 arg4 =
  Exp.apply ~loc:loc (id funname loc) [
      Labelled "count",Exp.constant (Pconst_integer ("1000",None));
      Labelled "name",Exp.constant (Pconst_string (title,None));
      Nolabel,gen;
      Nolabel,(id arg1 loc);
      Nolabel,(id arg2 loc);
      Nolabel, arg3;
      Nolabel, arg4
 ]

let commut_test loc funname gen : structure_item =
  let fname,_,_ = get_pos_info loc.loc_start in
  let testname = "commutativity test of "^funname^" in file "^fname in
  let test = call loc "commut" testname gen funname in
  let desc = wild_card_declaration test in
  {pstr_desc=desc;pstr_loc = loc}

let assoc_test loc funname gen : structure_item =
  let fname,_,_ = get_pos_info loc.loc_start in
  let testname = "associativity test of "^funname^" in file "^fname in
  let test = call loc "assoc" testname gen funname in
  let desc = wild_card_declaration test in
  {pstr_desc=desc;pstr_loc = loc}

let distrib_test loc funname1 funname2 gen : structure_item =
  let fname,_,_ = get_pos_info loc.loc_start in
  let testname = "distributivity test of "^funname1^" in file "^fname^" over"^funname2 in
  let test = call2 loc "distrib" testname gen funname1 funname2   in
  let desc = wild_card_declaration test in
  {pstr_desc=desc;pstr_loc = loc}

let over_approx_test loc funname1 funname2 in_g rand_g gen : structure_item =
  let fname,_,_ = get_pos_info loc.loc_start in
  let testname = " that "^funname1^" in file "^fname^" over-approximates "^funname2 in
  let test = call4 loc "over_approx2" testname gen funname1 funname2 in_g rand_g in
  let desc = wild_card_declaration test in
  {pstr_desc=desc;pstr_loc = loc}

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
  let str = Stream.of_list attr in
  let rec loop state acc =
    match Stream.next str |> helper with
    | "in_gamma",[] ->
       loop {state with in_gamma = Some (id funname loc)} acc
    | "rand_gamma",[] ->
       loop {state with rand_gamma = Some (id funname loc)} acc
    | "gen",[] ->
       loop {state with gen = Some (id funname loc)} acc
    | "gen",[{pstr_desc=Pstr_eval (e,_);_}] ->
       loop {state with gen = Some e} acc
    | "commut",[] ->
       let t = commut_test loc funname (get_gen state) in
       loop state (t::acc)
    | "assoc",[] ->
       let t = assoc_test loc funname (get_gen state) in
       loop state (t::acc)
    | "distrib",[{pstr_desc=Pstr_eval ({pexp_desc=Pexp_ident id;_},_);_}] ->
       let t = distrib_test loc funname (Longident.last id.txt) (get_gen state) in
       loop state (t::acc)
    | "over_approx", [{pstr_desc=Pstr_eval ({pexp_desc=Pexp_ident id;_},_);_}]->
       let t = over_approx_test loc funname
                 (Longident.last id.txt)
                 (get_in_gamma state)
                 (get_rand_gamma state)
                 (get_gen state) in
       loop state (t::acc)
    | _ -> loop state acc
    | exception Stream.Failure -> acc,state
  and helper a =
    match a.attr_payload with
    | PStr x -> a.attr_name.txt,x
    | _ -> failwith "invalid payload"
  in
  loop state []

let testify_mapper =
  let handle_str mapper =
    let rec aux state res = function
      | [] -> List.rev res
      | ({pstr_desc=
            Pstr_value(_,[
                  {pvb_pat={ppat_desc=Ppat_var ({txt=funname;_});ppat_loc=loc;_}
                  ;pvb_attributes=(_::_ as attr);_}]);_} as h)::tl ->
         let tests,state = gather_tests state loc funname attr in
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
