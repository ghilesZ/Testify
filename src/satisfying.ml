open Migrate_parsetree
open Ast_410
open Parsetree
open Ast_mapper
open Ast_helper
open Helper
open State

(* number of generation per test *)
let number = ref 10000

let set_number = ( := ) number

let add_test args = apply_runtime "add_test" args |> Str.eval

let run = apply_runtime "run_test" [unit] |> Str.eval

(* test generation for constants *)
let test_constant (name : string) loc (f : expression) =
  let f = lambda_s "_" (apply_nolbl f [exp_id name]) in
  let n = Format.asprintf "constant: %s in %s" (bold_blue name) (blue loc) in
  add_test [one; string_ n; exp_id "QCheck.unit"; f]

(* generation of QCheck test *)
let test (name : string) (args : expression list) =
  add_test ([int_ !number; string_ name] @ args)

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
        [ apply_lab_nolab_s "QCheck.make"
            [("print", apply_runtime_1 "opt_print" (exp_id "snd"))]
            [apply_runtime_1 "opt_gen" go]
        ; apply_runtime_1 "sat_output" satisfy ]

(* generic derivation function for core types *)
let derive_ctype env compose =
  let rec aux ct =
    match ct.ptyp_desc with
    | Ptyp_var s -> Types.find_opt (lparse s) env
    | Ptyp_constr ({txt; _}, []) -> Types.find_opt txt env
    | Ptyp_poly ([], ct) -> aux ct
    | Ptyp_tuple tup -> (
      try Some (compose (List.map aux tup)) with Invalid_argument _ -> None )
    | _ -> None
  in
  aux

let default_printer = lambda_s "_" (string_ (gray "undefined"))

(* builds a n-tuple generator from a list of n generators *)
let gen_tuple gens =
  List.map (fun g -> apply_nolbl (Option.get g) [exp_id "x"]) gens
  |> Exp.tuple |> lambda_s "x"

(* builds a n-tuple printer from a list of n printers *)
let print_tuple printers =
  let get_name = id_gen_gen () in
  let np p =
    let n, id = get_name () in
    (apply_nolbl (Option.value ~default:default_printer p) [id], pat_s n)
  in
  let names, pats = List.split (List.map np printers) in
  let b = string_concat ~sep:", " names in
  let b' = string_concat [string_ "("; b; string_ ")"] in
  lambda (Pat.tuple pats) b'

let get_gen s = derive_ctype State.(s.gens) gen_tuple

let get_print s = derive_ctype State.(s.prints) print_tuple

let get_prop s =
  derive_ctype
    State.(s.props)
    (fun props ->
      let get_name = id_gen_gen () in
      let compose (pats, prop) p =
        match (prop, p) with
        | x, None -> (Pat.any () :: pats, x)
        | None, Some p ->
            let name, id = get_name () in
            let app = apply_nolbl p [id] in
            (pat_s name :: pats, Some app)
        | Some p', Some p ->
            let name, id = get_name () in
            let app = apply_nolbl p' [id] in
            (pat_s name :: pats, Some (apply_nolbl_s "( && )" [p; app]))
      in
      let pats, body = List.fold_left compose ([], None) props in
      lambda (Pat.tuple (List.rev pats)) (Option.get body))

(* generic derivation function for type declaration *)
let derive_decl (s : State.t) get_f field_f record_f constr_f sum_f sat_f
    ({ptype_kind; ptype_manifest; ptype_attributes; _} as td) =
  let field_f f =
    let field = get_f s f.pld_type |> Option.get in
    field_f field f.pld_name.txt
  in
  try
    match get_attribute_pstr "satisfying" ptype_attributes with
    | Some e -> sat_f td e
    | None -> (
      match ptype_kind with
      | Ptype_abstract -> Option.(join (map (get_f s) ptype_manifest))
      | Ptype_variant constructors ->
          let constr_f c =
            match c.pcd_args with
            | Pcstr_tuple ct ->
                Some (constr_f (List.map (get_f s) ct) c.pcd_name)
            | Pcstr_record _labs -> None
          in
          Some (sum_f (List.map constr_f constructors))
      | Ptype_record labs -> Some (record_f (List.map field_f labs))
      | Ptype_open -> None )
  with Invalid_argument _ -> None

let rec get_generator s =
  derive_decl s get_gen
    (fun gen name -> (lid_loc name, apply_nolbl gen [exp_id "rs"]))
    (fun fields ->
      let app = Exp.record fields None in
      lambda_s "rs" app)
    (fun gs n ->
      match gs with
      | [] -> lambda_s "_" (Exp.construct (lid_loc n.txt) None)
      | l ->
          lambda_s "rs"
            (Exp.construct (lid_loc n.txt)
               (Some (apply_nolbl (gen_tuple l) [string_ "rs"]))))
    (fun _ -> invalid_arg "")
    (fun td e ->
      let rejection pred gen = apply_runtime "reject" [pred; gen] in
      match Gegen.solve_td td e with
      | None ->
          Option.map (rejection e)
            (get_generator s {td with ptype_attributes= []})
      | x -> x)

(* Given a rewritting state [rs] and and a type [t], search for the printer
   associated to [t] in [rs]. Returns a Parsetree.expression (corresponding
   to a printer) option. *)
let get_printer s td =
  let rec aux s td =
    derive_decl s get_print
      (fun print name ->
        let field = apply_nolbl print [exp_id name] in
        let field_name = string_ name in
        ( string_concat ~sep:"=" [field_name; field]
        , (lid_loc name, pat_s name) ))
      (fun l ->
        let fields, pat = List.split l in
        let app = string_concat ~sep:"; " fields in
        let app = string_concat [string_ "{"; app; string_ "}"] in
        lambda (Pat.record pat Closed) app)
      (fun p n : case ->
        match p with
        | [] -> Exp.case (Pat.variant n.txt None) (string_ n.txt)
        | p ->
            let id = id_gen_gen () in
            let pat, exp =
              List.map
                (fun _ ->
                  let p, e = id () in
                  (pat_s p, e))
                p
              |> List.split
            in
            Exp.case
              (Pat.variant n.txt (Some (Pat.tuple pat)))
              (apply_nolbl (print_tuple p) [Exp.tuple exp]))
      (fun (cl : case option list) ->
        lambda_s "x"
          (Exp.match_ (exp_id "x")
             (List.map
                (function
                  | None -> Exp.case (Pat.any ()) default_printer
                  | Some c -> c)
                cl)))
      (fun td _ -> aux s {td with ptype_attributes= []})
      td
  in
  aux s td |> Option.value ~default:default_printer

(* gets the property attached to the type [t] in [rs] (or None) *)
let rec get_property (t : core_type) (s : State.t) : expression option =
  match t.ptyp_desc with
  | Ptyp_constr ({txt; _}, []) -> Types.find_opt txt s.props
  | Ptyp_poly ([], ct) -> get_property ct s
  | _ -> None

let derive (s : State.t) (td : type_declaration) =
  let infos = (get_generator s td, get_printer s td, None) in
  let id = lparse td.ptype_name.txt in
  State.update s id infos

(* restriction: we force the same (structurally equal) pattern to appear on
   both type declarations *)
let compose_properties e1 e2 =
  match (e1.pexp_desc, e2.pexp_desc) with
  | Pexp_fun (l1, o1, p1, e1), Pexp_fun (l2, o2, p2, e2) ->
      if p1 = p2 && l1 = l2 && o1 = o2 then
        let pred = Pexp_fun (l1, o1, p1, apply_nolbl_s "( && )" [e1; e2]) in
        {e1 with pexp_desc= pred}
      else failwith "properties should have same pattern"
  | _ -> failwith "properties should be functions"

(* update the rewritting state according to a type declaration *)
let declare_type state t =
  let state = derive state t in
  match get_attribute_pstr "satisfying" t.ptype_attributes with
  | None -> state
  | Some e -> register_prop state (lparse t.ptype_name.txt) e

(* annotation handling *)
let check_gen vb (s : State.t) : State.t =
  match get_attribute_pstr "gen" vb.pvb_attributes with
  | None -> s
  | Some {pexp_desc= Pexp_ident l; _} -> register_gen s l.txt vb.pvb_expr
  | _ -> failwith "bad gen attribute"

let check_print vb (s : State.t) =
  match get_attribute_pstr "print" vb.pvb_attributes with
  | None -> s
  | Some {pexp_desc= Pexp_ident l; _} -> register_print s l.txt vb.pvb_expr
  | _ -> failwith "bad print attribute"

let get_infos (s : State.t) e =
  let helper pat =
    match pat.ppat_desc with
    | Ppat_constraint (_, t) -> (get_gen s t, get_print s t)
    | _ -> (None, None)
  in
  let rec aux res = function
    | Pexp_fun (Nolabel, None, pat, exp) -> (
      match helper pat with
      | Some g, Some p -> aux ((g, p) :: res) exp.pexp_desc
      | _ -> raise Exit )
    | Pexp_constraint (_, ct) -> (List.rev res, ct)
    | _ -> raise Exit
  in
  try Some (aux [] e) with Exit -> None

(* compute a list of tests to be added to the AST. handles: explicitly typed
   constants and (fully) explicitly typed functions *)
let gather_tests vb state =
  let loc = Format.asprintf "%a" Location.print_loc vb.pvb_loc in
  match vb.pvb_pat.ppat_desc with
  (* let constant:typ = val*)
  | Ppat_constraint ({ppat_desc= Ppat_var {txt; _}; _}, typ) ->
      get_property typ state
      |> Option.fold ~none:[] ~some:(fun p -> [test_constant txt loc p])
  (* let fn (arg1:typ1) (arg2:typ2) ... : return_typ = body *)
  | Ppat_var {txt; _} -> (
    match get_infos state vb.pvb_expr.pexp_desc with
    | None -> []
    | Some (args, ct) ->
        let out_print =
          get_print state ct |> Option.value ~default:default_printer
        in
        let name = Format.asprintf "%s in %s" (bold_blue txt) (blue loc) in
        get_property ct state |> Option.to_list
        |> List.map (generate txt args out_print name) )
  | _ -> []

(* actual mapper *)
let mapper =
  let handle_str mapper str =
    let rec aux state res = function
      | [] -> List.rev (run :: res)
      (* type declaration *)
      | ({pstr_desc= Pstr_type (_, [t]); _} as h) :: tl ->
          aux (declare_type state t) (h :: res) tl
      (* value declaration *)
      | ({pstr_desc= Pstr_value (_, [pvb]); _} as h) :: tl ->
          let tests = gather_tests pvb state in
          let state = state |> check_gen pvb |> check_print pvb in
          let h' = mapper.structure_item mapper h in
          aux state (tests @ (h' :: res)) tl
      | h :: tl -> aux state (h :: res) tl
    in
    aux State.s0 [] str
  in
  {default_mapper with structure= handle_str}
