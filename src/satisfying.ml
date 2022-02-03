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

let set_seed x = seed := Some x

(* test generation for constants *)
let test_constant (name : string) (loc : Location.t) (f : expression) =
  let loc = Format.asprintf "%a" Location.print_loc loc in
  let f = lambda_s "_" (apply_nolbl f [exp_id name]) in
  letunit
    (open_runtime
       (apply_nolbl_s "add_const" [one; string_ name; string_ loc; f]) )

(* test generation for functions *)
let test (name : string) (loc : Location.t) (args : expression list) =
  let loc = Format.asprintf "%a" Location.print_loc loc in
  letunit
    (open_runtime
       (apply_nolbl_s "add_fun"
          ([int_ !number; string_ name; string_ loc] @ args) ) )

(* call to set_seed *)
let gen_set_seed (x : int) = letunit (apply_runtime "set_seed" [int_ x])

(* call to run_test*)
let run () = letunit (apply_runtime "run_test" [unit])

(* function application generator *)
let generate (fn : string) loc args out_print satisfy =
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
      test fn loc
        [ apply_nolbl_s "opt_print" [exp_id "snd"]
        ; apply_nolbl_s "opt_gen" [go]
        ; apply_nolbl_s "sat_output" [satisfy] ]

(**************)
(* Derivation *)
(**************)

(** True if and only if the type has the [@collect] attribute. *)
let is_collected (ct : Parsetree.core_type) : bool =
  Helper.has_attribute "collect" ct.ptyp_attributes

(* let rec apply_decl state params (poly : Typrepr.param) =
 *   let args = List.combine poly.vars params in
 *   match poly.body.ptype_kind with
 *   | Ptype_abstract ->
 *       { poly.body with
 *         ptype_manifest=
 *           Option.map (apply_ctype state args) poly.body.ptype_manifest }
 *   | Ptype_variant constructors ->
 *       let constr_f c =
 *         match c.pcd_args with
 *         | Pcstr_tuple cts ->
 *             { c with
 *               pcd_args= Pcstr_tuple (List.map (apply_ctype state args) cts)
 *             }
 *         | Pcstr_record _labs ->
 *             Log.warn "Inline records are not supported" ;
 *             raise Exit
 *       in
 *       { poly.body with
 *         ptype_kind= Ptype_variant (List.map constr_f constructors) }
 *   | Ptype_record labs ->
 *       let lab_f l = {l with pld_type= apply_ctype args state l.pld_type} in
 *       {poly.body with ptype_kind= Ptype_record (List.map lab_f labs)}
 *   | Ptype_open -> poly.body
 *
 * and apply_ctype state args ct =
 *   match ct.ptyp_desc with
 *   | Ptyp_var var -> List.assoc var args
 *   | Ptyp_constr (_, []) -> ct
 *   | Ptyp_constr (name, l) ->
 *       { ct with
 *         ptyp_desc= Ptyp_constr (name, List.map (apply_ctype state args) l) }
 *   | Ptyp_poly (_, ct) -> apply_ctype state args ct
 *   | Ptyp_tuple tup ->
 *       {ct with ptyp_desc= Ptyp_tuple (List.map (apply_ctype state args) tup)}
 *   | Ptyp_arrow (l, i, o) ->
 *       { ct with
 *         ptyp_desc=
 *           Ptyp_arrow (l, apply_ctype state args i, apply_ctype state args o)
 *       }
 *   | _ -> ct *)

(* derivation function for type declaration *)
let rec derive_decl (s : Module_state.t) params
    ({ptype_kind; ptype_manifest; ptype_attributes; _} as td) : Typrepr.t =
  match get_attribute_pstr "satisfying" ptype_attributes with
  | Some e ->
      Typrepr.Constrained.make_td td
        (derive_decl s params {td with ptype_attributes= []})
        e
  | None -> (
    match ptype_kind with
    | Ptype_abstract ->
        Option.fold
          ~none:(Typrepr.empty td.ptype_name.txt)
          ~some:(derive_ctype s params) ptype_manifest
    | Ptype_variant constructors ->
        let constr_f c =
          match c.pcd_args with
          | Pcstr_tuple cts ->
              ( c.pcd_name.txt
              , List.map
                  (fun ct -> (derive_ctype s params ct, is_collected ct))
                  cts )
          | Pcstr_record _labs ->
              Log.warn "Inline records are not supported" ;
              raise Exit
        in
        Typrepr.Sum.make td.ptype_name.txt (List.map constr_f constructors)
    | Ptype_record labs ->
        let lab_f l = (l.pld_name.txt, derive_ctype s params l.pld_type) in
        Typrepr.Record.make (List.map lab_f labs)
    | Ptype_open -> Typrepr.empty td.ptype_name.txt )

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
    | _ -> Typrepr.empty (Format.asprintf "%a" print_coretype ct) )

let derive state (recflag, typs) =
  Log.type_decl (recflag, typs) ;
  (* we pre-fill the environment with the type being processed (for recursive
     types)*)
  let rec_, nonrec_ = rec_nonrec recflag typs in
  let state =
    List.fold_left
      (fun acc td ->
        Module_state.update acc
          (lparse td.ptype_name.txt)
          (Typrepr.Rec.make td.ptype_name.txt) )
      state rec_
  in
  let is_rec td =
    List.exists (fun td' -> td'.ptype_name.txt = td.ptype_name.txt) rec_
  in
  (* we build the bodies of the functions *)
  let state, later =
    List.fold_left
      (fun (acc, later) td ->
        let id = lparse td.ptype_name.txt in
        match td.ptype_params with
        | [] ->
            let typrepr = derive_decl acc [] td in
            if is_rec td then (acc, (id, typrepr) :: later)
            else (Module_state.update acc id typrepr, later)
        | _ -> (Module_state.update_param state id td, later) )
      (state, []) typs
  in
  (* Registering recursive functions is delayed so as to avoid inlining the body
     of their generators within each other. *)
  let state =
    List.fold_left
      (fun state (id, typ) -> Module_state.update state id typ)
      state later
  in
  List.iter
    (fun td ->
      let id = lparse td.ptype_name.txt in
      match td.ptype_params with
      | [] ->
          let typrepr = Module_state.get id state |> Option.get in
          Log.print "%a\n%!" Typrepr.print typrepr
      | _ -> () )
    nonrec_ ;
  (* we wrap them into a recursive function *)
  let mono_typs, poly_typs, glb_constr =
    List.fold_left
      (fun (mono, poly, glb_constr) td ->
        match td.ptype_params with
        | [] ->
            let name = td.ptype_name.txt in
            let typ =
              match Module_state.get (lparse name) state with
              | Some typ -> typ
              | None -> exit 1
            in
            let glb_constr =
              match get_attribute_pstr "satisfying" td.ptype_attributes with
              | Some e -> (
                match (glb_constr, GlobalConstraint.search e) with
                | Some _, Some _ ->
                    failwith
                      "Found two global contraints, please only specify one"
                | None, (Some _ as g) -> g
                | _, None ->
                    Format.ksprintf failwith
                      "I didn't understand the global constraint for\n\
                      \            type %s" td.ptype_name.txt )
              | None -> glb_constr
            in
            ((name, typ) :: mono, poly, glb_constr)
        | _ -> (mono, td :: poly, glb_constr) )
      ([], [], None) rec_
  in
  let mono_typs =
    match mono_typs with
    | [] -> []
    | _ -> Typrepr.Rec.finish glb_constr (List.rev mono_typs)
  in
  let state =
    List.fold_left
      (fun state td ->
        let id = lparse td.ptype_name.txt in
        Module_state.update_param state id td )
      state poly_typs
  in
  List.fold_left
    (fun state (name, typ) ->
      Log.print "%a\n%!" Typrepr.print typ ;
      Module_state.update state (lparse name) typ )
    state mono_typs

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
        (* accepts to omit the explicit type annotation for the unit pattern*)
        let u = Option.get (Module_state.get (lparse "unit") s) in
        (u.gen |> Option.get, u.print)
    | Ppat_constraint (_, t) -> (
        let ct = derive_ctype s [] t in
        match ct.gen with
        | None ->
            Log.print "Missing generator for type `%a`\n%!" print_coretype t ;
            raise Exit
        | Some g -> (g, ct.print) )
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

(* builds a test list to add to the AST. handles explicitly typed values *)
let gather_tests vb state =
  match vb.pvb_pat.ppat_desc with
  (* let constant:typ = val*)
  | Ppat_constraint ({ppat_desc= Ppat_var {txt; _}; _}, typ) -> (
      Log.print " #### Declaration of typed constant: *%s*\n" (md txt) ;
      let info = derive_ctype state [] typ in
      Log.print "Type: `%a`%!" print_coretype typ ;
      match info with
      | {spec= Some p; _} ->
          Log.print " is attached a specification. Generating a test.\n%!" ;
          [test_constant txt vb.pvb_loc p]
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
          | {spec= Some prop; _} ->
              Log.print
                " is attached a specification. Generating a test.\n%!" ;
              [generate txt vb.pvb_loc args info.print prop]
          | _ ->
              Log.print " is not attached a specification.\n%!" ;
              [] ) )
  | _ -> []

let runtime = ref true

(* actual mapper *)
let mapper =
  let in_attr = ref 0 in
  let state = ref (Module_state.load ()) in
  let handle_str mapper str =
    let rec aux res = function
      | [] ->
          (* end of structure, we run the collected tests*)
          let t =
            match !seed with None -> res | Some x -> gen_set_seed x :: res
          in
          List.rev (if !in_attr > 0 then res else run () :: t)
      (* type declaration *)
      | ({pstr_desc= Pstr_type (recflag, types); pstr_loc; _} as h) :: tl ->
          Helper.update_loc pstr_loc ;
          state := derive !state (recflag, types) ;
          aux ({h with pstr_loc= !current_loc} :: res) tl
      (* value declaration *)
      | ({pstr_desc= Pstr_value (_, [pvb]); pstr_loc; _} as h) :: tl ->
          Helper.update_loc pstr_loc ;
          let tests = gather_tests pvb !state in
          (* let s = global |> check_gen pvb |> check_print pvb in *)
          let h' = mapper.structure_item mapper h in
          aux (tests @ ({h' with pstr_loc= !current_loc} :: res)) tl
      | h :: tl ->
          Helper.update_loc h.pstr_loc ;
          let h' = mapper.structure_item mapper h in
          aux ({h' with pstr_loc= !current_loc} :: res) tl
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
    Helper.update_loc module_.pmb_loc ;
    let res = default_mapper.module_binding mapper module_ in
    state := Module_state.end_ !state ;
    {res with pmb_loc= module_.pmb_loc}
  in
  { default_mapper with
    structure= handle_str
  ; attribute= handle_attr
  ; module_binding= handle_module }
