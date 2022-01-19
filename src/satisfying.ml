open Migrate_parsetree.Ast_410
open Parsetree
open Ast_mapper
open Helper
open Asttypes

(*******************)
(* Test management *)
(*******************)

(* number of generation per test *)
let number = ref 10000

(* seed for reproducibility*)
let seed : int option ref = ref None

let gen_set_seed x = seed := Some x

(* test generation for constants *)
let test_constant (name : string) loc (f : expression) =
  let f = lambda_s "_" (apply_nolbl f [exp_id name]) in
  let n = Format.asprintf "constant: %s in %s" (bold_blue name) (blue loc) in
  letunit (open_runtime (apply_nolbl_s "add_const" [one; string_ n; f]))

(* test generation for functions *)
let test (name : string) args =
  letunit
    (open_runtime
       (apply_nolbl_s "add_fun" ([int_ !number; string_ name] @ args)) )

(* call to set_seed *)
let set_seed x = letunit (apply_runtime "set_seed" [int_ x])

(* call to run_test*)
let run () = letunit (apply_runtime "run_test" [unit])

(* function application generator *)
let generate fn args out_print testname satisfy =
  let testname = Format.asprintf "function: %s" testname in
  let get_name = id_gen_gen () in
  let args =
    List.map
      (fun (g, p) ->
        let name, id = get_name () in
        (let_ name (apply_nolbl g [exp_id "rs"]), apply_nolbl p [id], name)
        )
      args
  in
  match args with
  | [] -> invalid_arg "generate on empty list"
  | (g, s, n) :: tl ->
      let letin, str, args =
        List.fold_left
          (fun (l1, s1, args) (l2, s2, arg) ->
            ( (fun x -> l1 (l2 x))
            , string_concat ~sep:" " [s1; s2]
            , exp_id arg :: args ) )
          (g, s, [exp_id n])
          tl
      in
      let str = string_concat [string_ ("(" ^ fn ^ " "); str; string_ ")"] in
      let no, id = get_name () in
      let leto x = letin (let_ no (apply_nolbl_s fn (List.rev args)) x) in
      let go =
        string_concat ~sep:" = " [str; apply_nolbl out_print [id]]
        |> pair id |> leto |> lambda_s "rs"
      in
      test testname
        [ apply_nolbl_s "opt_print" [exp_id "snd"]
        ; apply_nolbl_s "opt_gen" [go]
        ; apply_nolbl_s "sat_output" [satisfy] ]

(**************)
(* Derivation *)
(**************)

(* derivation function for type declaration *)
let rec derive_decl (s : Module_state.t) params
    ({ptype_kind; ptype_manifest; ptype_attributes; _} as td) : Typrepr.t =
  try
    match get_attribute_pstr "satisfying" ptype_attributes with
    | Some e ->
        Typrepr.Constrained.make_td td
          (derive_decl s params {td with ptype_attributes= []})
          e
    | None -> (
      match ptype_kind with
      | Ptype_abstract ->
          Option.fold ~none:Typrepr.empty ~some:(derive_ctype s params)
            ptype_manifest
      | Ptype_variant constructors ->
          let constr_f c =
            match c.pcd_args with
            | Pcstr_tuple ct ->
                (c.pcd_name, List.map (derive_ctype s params) ct)
            | Pcstr_record _labs -> raise Exit
          in
          Typrepr.Sum.make (List.map constr_f constructors)
      | Ptype_record labs ->
          let labs =
            List.map
              (fun {pld_name; pld_type; _} ->
                (pld_name.txt, derive_ctype s params pld_type) )
              labs
          in
          Typrepr.Record.make labs
      | Ptype_open -> Typrepr.empty )
  with Invalid_argument _ | Exit -> Typrepr.empty

(* derivation function for core types *)
and derive_ctype (state : Module_state.t) params ct : Typrepr.t =
  match get_attribute_pstr "satisfying" ct.ptyp_attributes with
  | Some e ->
      Typrepr.Constrained.make ct
        (derive_ctype state params {ct with ptyp_attributes= []})
        e
  | None -> (
    match ct.ptyp_desc with
    | Ptyp_var var -> List.assoc var params
    | Ptyp_constr ({txt; _}, []) -> Module_state.get txt state |> Option.get
    | Ptyp_constr ({txt; _}, l) ->
        let p = Module_state.get_param txt state |> Option.get in
        let env = State.get_env p (List.map (derive_ctype state params) l) in
        let t = derive_decl state env p.body in
        Log.print "Building type `%a`:\n%a\n" print_coretype ct Typrepr.print
          t ;
        t
    | Ptyp_poly (_, ct) -> derive_ctype state params ct
    | Ptyp_tuple tup ->
        Typrepr.Product.make (List.map (derive_ctype state params) tup)
    | Ptyp_arrow (Nolabel, input, output) ->
        let input = derive_ctype state params input in
        let output = derive_ctype state params output in
        Typrepr.Arrow.make input output
    | _ -> Typrepr.empty )

(** {1 annotation handling} *)
let check_gen vb (s : State.t) : State.t =
  match get_attribute_pstr "gen" vb.pvb_attributes with
  | None -> s
  | Some {pexp_desc= Pexp_ident l; _} ->
      Log.print "Setting %a as a generator for %a\n%!" print_pat vb.pvb_pat
        print_longident l.txt ;
      State.register_gen s l.txt vb.pvb_expr
  | _ -> failwith "bad gen attribute"

let check_print vb (s : State.t) =
  match get_attribute_pstr "print" vb.pvb_attributes with
  | None -> s
  | Some {pexp_desc= Pexp_ident l; _} ->
      Log.print "setting %a as a printer for %a\n%!" print_pat vb.pvb_pat
        print_longident l.txt ;
      State.register_print s l.txt vb.pvb_expr
  | _ -> failwith "bad print attribute"

let get_infos (s : Module_state.t) e =
  let open Typrepr in
  let get_gen_print pat =
    match pat.ppat_desc with
    | Ppat_construct ({txt= Lident "()"; _}, _) ->
        (* allow to omit the explicit type annotation for the unit pattern*)
        let {gen; print; _} =
          Option.get (Module_state.get (lparse "unit") s)
        in
        (gen |> Option.get, print |> Option.get)
    | Ppat_constraint (_, t) -> (
        let {gen; print; _} = derive_ctype s [] t in
        match (gen, print) with
        | None, None ->
            Log.print "Missing generator and printer for type `%a`\n%!"
              print_coretype t ;
            raise Exit
        | None, _ ->
            Log.print "Missing generator for type `%a`\n%!" print_coretype t ;
            raise Exit
        | _, None ->
            Log.print "Missing printer for type `%a`\n%!" print_coretype t ;
            raise Exit
        | Some g, Some p -> (g, p) )
    | _ ->
        Log.print "Missing type annotation for argument `%a`\n%!" print_pat
          pat ;
        raise Exit
  in
  let rec aux res = function
    | Pexp_fun (Nolabel, None, pat, exp) ->
        aux (get_gen_print pat :: res) exp.pexp_desc
    | Pexp_constraint (_, ct) -> (List.rev res, ct)
    | _ -> raise Exit
  in
  try
    let infos, ct = aux [] e in
    Some (infos, ct)
  with Exit | Invalid_argument _ -> None

let derive state (recflag, typs) =
  Log.type_decl (recflag, typs) ;
  (* we pre-fill the environment with the type being processed (for recursive
     types)*)
  let state =
    match recflag with
    | Recursive ->
        List.fold_left
          (fun acc td ->
            Module_state.update acc
              (lparse td.ptype_name.txt)
              (Typrepr.make_rec td.ptype_name.txt) )
          state typs
    | Nonrecursive -> state
  in
  (* we build the bodies of the functions *)
  let state =
    List.fold_left
      (fun acc td ->
        let id = lparse td.ptype_name.txt in
        match td.ptype_params with
        | [] ->
            let typrepr = derive_decl acc [] td in
            Module_state.update acc id typrepr
        | _ -> Module_state.update_param state id td )
      state typs
  in
  (* we wrap them into a recursive function *)
  List.fold_left
    (fun acc td ->
      let id = lparse td.ptype_name.txt in
      let res =
        match td.ptype_params with
        | [] ->
            let typrepr =
              Module_state.get id acc |> Option.get
              |> Typrepr.finish_rec td.ptype_name.txt
            in
            Log.print "%a\n%!" Typrepr.print typrepr ;
            Module_state.update acc id typrepr
        | _ -> Module_state.update_param state id td
      in
      Log.print "\n\n\n" ; res )
    state
    (recursive (recflag, typs))

(* builds a test list to add to the AST. handles explicitly typed values *)
let gather_tests vb state =
  let loc = Format.asprintf "%a" Location.print_loc vb.pvb_loc in
  match vb.pvb_pat.ppat_desc with
  (* let constant:typ = val*)
  | Ppat_constraint ({ppat_desc= Ppat_var {txt; _}; _}, typ) -> (
      Log.print " #### Declaration of typed constant: *%s*\n" (md txt) ;
      let info = derive_ctype state [] typ in
      Log.print "Type: `%a`%!" print_coretype typ ;
      match info with
      | {spec= Some p; _} ->
          Log.print " is attached a specification. Generating a test.\n%!" ;
          [test_constant txt loc p]
      | _ ->
          Log.print " is not attached a specification.\n%!" ;
          [] )
  (* let fn (arg1:typ1) (arg2:typ2) ... : return_typ = body *)
  | Ppat_var {txt; _} -> (
      Log.print "#### Declaration of a value *%s*\n%!" (md txt) ;
      match get_infos state vb.pvb_expr.pexp_desc with
      | None ->
          Log.print "Missing requirement for value `%s`\n%!" txt ;
          []
      | Some (args, ct) -> (
          let info = derive_ctype state [] ct in
          Log.print "Return type `%a`%!" print_coretype ct ;
          match info with
          | {spec= Some prop; print= Some p; _} ->
              Log.print
                " is attached a specification. Generating a test.\n%!" ;
              let name =
                Format.asprintf "%s in %s" (bold_blue txt) (blue loc)
              in
              [generate txt args p name prop]
          | _ ->
              Log.print " is not attached a specification.\n%!" ;
              [] ) )
  | _ -> []

(* actual mapper *)
let mapper =
  let in_attr = ref 0 in
  let state = ref (Module_state.load ()) in
  let handle_str mapper str =
    let rec aux res = function
      | [] ->
          (* end of structure, we run the collected tests*)
          let t =
            match !seed with None -> res | Some x -> set_seed x :: res
          in
          List.rev (if !in_attr > 0 then res else run () :: t)
      (* type declaration *)
      | ({pstr_desc= Pstr_type (recflag, types); _} as h) :: tl ->
          state := derive !state (recflag, types) ;
          aux (h :: res) tl
      (* value declaration *)
      | ({pstr_desc= Pstr_value (_, [pvb]); _} as h) :: tl ->
          let tests = gather_tests pvb !state in
          (* let s = global |> check_gen pvb |> check_print pvb in *)
          let h' = mapper.structure_item mapper h in
          aux (tests @ (h' :: res)) tl
      | h :: tl -> aux (mapper.structure_item mapper h :: res) tl
    in
    aux [] str
  in
  let handle_attr m a =
    (* deactivate test generation in attributes *)
    incr in_attr ;
    let res = default_mapper.attribute m a in
    decr in_attr ; res
  in
  let handle_module mapper module_ =
    let name = match module_.pmb_name.txt with None -> "_" | Some s -> s in
    state := Module_state.begin_ !state name ;
    let res = default_mapper.module_binding mapper module_ in
    state := Module_state.end_ !state ;
    res
  in
  { default_mapper with
    structure= handle_str
  ; attribute= handle_attr
  ; module_binding= handle_module }
