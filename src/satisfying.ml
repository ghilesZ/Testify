open Migrate_parsetree
open Ast_410
open Parsetree
open Ast_mapper
open Helper
open State

(** {1 AST management for test} *)

(* number of generation per test *)
let number = ref 10000

(* seed for reproducibility*)
let seed : int option ref = ref None

let set_seed x = seed := Some x

(* test generation for constants *)
let test_constant (name : string) loc (f : expression) =
  let f = lambda_s "_" (apply_nolbl f [exp_id name]) in
  let n = Format.asprintf "constant: %s in %s" (bold_blue name) (blue loc) in
  letunit (open_runtime (apply_nolbl_s "add_const" [one; string_ n; f]))

(* test generation for functions *)
let test (name : string) args =
  letunit
    (open_runtime
       (apply_nolbl_s "add_fun" ([int_ !number; string_ name] @ args)))

(* call to set_seed *)
let gen_set_seed x = letunit (apply_runtime "set_seed" [int_ x])

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
        (let_ name (apply_nolbl g [exp_id "rs"]), apply_nolbl p [id], name))
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
            , exp_id arg :: args ))
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

(* derivation function for type declaration *)
let rec derive_decl (s : State.t) paramenv
    ({ptype_kind; ptype_manifest; ptype_attributes; _} as td) =
  try
    match get_attribute_pstr "satisfying" ptype_attributes with
    | Some e ->
        Some
          (Typrepr.Constrained.make_td td
             ( derive_decl s paramenv {td with ptype_attributes= []}
             |> Option.get )
             e)
    | None -> (
      match ptype_kind with
      | Ptype_abstract ->
          Option.(join (map (derive_ctype s paramenv) ptype_manifest))
      | Ptype_variant constructors ->
          let constr_f c =
            match c.pcd_args with
            | Pcstr_tuple ct ->
                ( c.pcd_name
                , List.map
                    (fun ct -> derive_ctype s paramenv ct |> Option.get)
                    ct )
            | Pcstr_record _labs -> raise Exit
          in
          Some (Typrepr.Sum.make (List.map constr_f constructors))
      | Ptype_record labs ->
          let labs =
            List.map
              (fun {pld_name; pld_type; _} ->
                (pld_name.txt, derive_ctype s paramenv pld_type |> Option.get))
              labs
          in
          Some (Typrepr.Record.make labs)
      | Ptype_open -> None )
  with Invalid_argument _ | Exit -> None

(* derivation function for core types *)
and derive_ctype (state : State.t) paramenv ct =
  match get_attribute_pstr "satisfying" ct.ptyp_attributes with
  | Some e ->
      Option.map
        (fun t -> Typrepr.Constrained.make ct t e)
        (derive_ctype state paramenv {ct with ptyp_attributes= []})
  | None -> (
    match ct.ptyp_desc with
    | Ptyp_var var -> List.assoc_opt var paramenv
    | Ptyp_constr ({txt; _}, []) -> State.get txt state
    | Ptyp_constr ({txt; _}, l) -> (
        let p = State.get_param txt state in
        try
          Option.bind p (fun p ->
              let newenv =
                State.get_env p
                  (List.map
                     (fun ct ->
                       match derive_ctype state paramenv ct with
                       | Some t -> t
                       | _ -> raise Exit)
                     l)
              in
              match derive_decl state newenv p.body with
              | None -> raise Exit
              | Some t ->
                  Log.print "Building a representation for type `%a`:\n"
                    print_coretype ct ;
                  Log.print "%a\n%!" Typrepr.print t ;
                  Some t)
        with Exit -> None )
    | Ptyp_poly ([], ct) -> derive_ctype state paramenv ct
    | Ptyp_tuple tup -> (
      try
        Some
          (Typrepr.Product.make
             (List.map
                (fun t ->
                  match derive_ctype state paramenv t with
                  | Some t -> t
                  | _ -> raise Exit)
                tup))
      with Exit -> None )
    | _ -> None )

let derive (s : State.t) (td : type_declaration) =
  Log.print "### Declaration of type *%s*\n" td.ptype_name.txt ;
  Log.print "- Declaration:\n ```ocaml@.@[%a@]\n```\n" print_td td ;
  Log.print "- Kind: %s%s%s\n"
    ( if Option.is_none (get_attribute_pstr "satisfying" td.ptype_attributes)
    then ""
    else "constrained " )
    (if td.ptype_params = [] then "" else "polymorphic ")
    ( match td.ptype_kind with
    | Ptype_abstract -> "abstract type"
    | Ptype_variant _ -> "sum type"
    | Ptype_record _ -> "record type"
    | Ptype_open -> "extensible type" ) ;
  let id = lparse td.ptype_name.txt in
  let res =
    match td.ptype_params with
    | [] -> (
        let infos = derive_decl s [] td in
        match infos with
        | None ->
            Log.print "- No info found\n\n%!" ;
            s
        | Some infos ->
            Log.print "%a\n%!" Typrepr.print infos ;
            update s id infos )
    | _ -> update_param s id td
  in
  Log.print "\n\n\n" ; res

(** {1 annotation handling} *)
let check_gen vb (s : State.t) : State.t =
  match get_attribute_pstr "gen" vb.pvb_attributes with
  | None -> s
  | Some {pexp_desc= Pexp_ident l; _} ->
      Log.print "Setting %a as a generator for %a\n%!" print_pat vb.pvb_pat
        print_longident l.txt ;
      register_gen s l.txt vb.pvb_expr
  | _ -> failwith "bad gen attribute"

let check_print vb (s : State.t) =
  match get_attribute_pstr "print" vb.pvb_attributes with
  | None -> s
  | Some {pexp_desc= Pexp_ident l; _} ->
      Log.print "setting %a as a printer for %a\n%!" print_pat vb.pvb_pat
        print_longident l.txt ;
      register_print s l.txt vb.pvb_expr
  | _ -> failwith "bad print attribute"

let get_infos (s : State.t) e =
  let open Typrepr in
  let get_gen_print pat =
    match pat.ppat_desc with
    | Ppat_construct ({txt= Lident "()"; _}, _) ->
        (* allow to omit the explicit type annotation for the unit pattern*)
        let {gen; print; _} = Option.get (State.get (lparse "unit") s) in
        (gen |> Option.get, print |> Option.get)
    | Ppat_constraint (_, t) -> (
        let {gen; print; _} = Option.get (derive_ctype s [] t) in
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

(* compute a list of tests to be added to the AST. handles: explicitly typed
   constants and (fully) explicitly typed functions *)
let gather_tests vb state =
  let loc = Format.asprintf "%a" Location.print_loc vb.pvb_loc in
  match vb.pvb_pat.ppat_desc with
  (* let constant:typ = val*)
  | Ppat_constraint ({ppat_desc= Ppat_var {txt; _}; _}, typ) -> (
      Log.print " #### Declaration of typed constant: *%s*\n" (md txt) ;
      let info = derive_ctype state [] typ in
      Log.print "Type: `%a`%!" print_coretype typ ;
      match info with
      | Some {spec= Some p; _} ->
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
          Log.print "No type information for value `%s`\n%!" txt ;
          []
      | Some (args, ct) -> (
          let info = derive_ctype state [] ct in
          Log.print "Return type `%a`%!" print_coretype ct ;
          match info with
          | Some {spec= Some prop; print= Some p; _} ->
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
  let in_attribute = ref 0 in
  let handle_str mapper str =
    let rec aux res state = function
      | [] ->
          let t =
            match !seed with None -> res | Some x -> gen_set_seed x :: res
          in
          List.rev (if !in_attribute > 0 then res else run () :: t)
      (* type declaration *)
      | ({pstr_desc= Pstr_type (_, [t]); _} as h) :: tl ->
          aux (h :: res) (derive state t) tl
      (* value declaration *)
      | ({pstr_desc= Pstr_value (_, [pvb]); _} as h) :: tl ->
          let tests = gather_tests pvb state in
          let s = state |> check_gen pvb |> check_print pvb in
          let h' = mapper.structure_item mapper h in
          aux (tests @ (h' :: res)) s tl
      | h :: tl -> aux (mapper.structure_item mapper h :: res) state tl
    in
    ( match str with
    | [] -> ()
    | h :: _ ->
        let file, _, _ = Location.get_pos_info h.pstr_loc.loc_start in
        if file <> !Log.fn then (
          Log.set_output file ;
          Log.print "# File **%s**\n" file ) ) ;
    aux [] State.s0 str
  in
  let handle_attr m a =
    (* deactivate test generation in attributes *)
    incr in_attribute ;
    let res = default_mapper.attribute m a in
    decr in_attribute ; res
  in
  let handle_module mapper module_ =
    let res = default_mapper.module_binding mapper module_ in
    let file, _, _ = Location.get_pos_info module_.pmb_loc.loc_start in
    if file <> !Log.fn then (
      Log.set_output file ;
      Log.print "# File **%s**\n" file ) ;
    let name = match module_.pmb_name.txt with None -> "_" | Some s -> s in
    Log.print "## Module **%s**\n" name ;
    res
  in
  { default_mapper with
    structure= handle_str
  ; attribute= handle_attr
  ; module_binding= handle_module }
