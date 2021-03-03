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
  let f = lambda (Pat.any ()) (apply_nolbl f [exp_id name]) in
  let n = Format.asprintf "constant: %s in %s" (bold_blue name) (blue loc) in
  add_test [one; string_exp n; exp_id "QCheck.unit"; f]

(* generation of QCheck test *)
let test (name : string) (args : expression list) =
  add_test ([int_exp !number; string_exp name] @ args)

(* builds an input from a list of generators and printers and apply to it the
   function fn *)
let generate fn args testname satisfy =
  let rec aux (gen, print) pat args = function
    | [] -> (gen, print, pat, List.rev args)
    | (g, p) :: tl ->
        let name = get_name () in
        aux
          ( apply_nolbl_s "QCheck.Gen.pair" [gen; g]
          , apply_nolbl_s "QCheck.Print.pair" [print; p] )
          (Pat.tuple [pat; pat_s name])
          (exp_id name :: args) tl
  in
  let id = get_name () in
  let pat = pat_s id in
  let g, p, pat, args = aux (List.hd args) pat [exp_id id] (List.tl args) in
  let f = lambda pat ((satisfy @@@ exp_id fn) args) in
  let testname = Format.asprintf "function: %s" testname in
  test testname [apply_lab_nolab_s "QCheck.make" [("print", p)] [g]; f]

(* Core Type handling *)

(* generic derivation function *)
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

let get_gen s =
  derive_ctype
    State.(s.gens)
    (fun gens ->
      List.map (fun g -> apply_nolbl (Option.get g) [exp_id "x"]) gens
      |> Exp.tuple |> lambda_s "x")

let get_print s =
  derive_ctype
    State.(s.prints)
    (fun printers ->
      let np p =
        let n = get_name () in
        (apply_nolbl (Option.get p) [exp_id n], pat_s n)
      in
      let names, pats = List.split (List.map np printers) in
      let b = string_concat ~sep:", " names in
      let b' = string_concat [string_exp "("; b; string_exp ")"] in
      lambda (Pat.tuple pats) b')

let get_prop s =
  derive_ctype
    State.(s.props)
    (fun props ->
      let compose (pats, prop) p =
        match (prop, p) with
        | x, None -> (Pat.any () :: pats, x)
        | None, Some p ->
            let id = get_name () in
            let app = apply_nolbl p [exp_id id] in
            (pat_s id :: pats, Some app)
        | Some p', Some p ->
            let id = get_name () in
            let app = apply_nolbl p' [exp_id id] in
            (pat_s id :: pats, Some (apply_nolbl_s "( && )" [p; app]))
      in
      let pats, body = List.fold_left compose ([], None) props in
      lambda (Pat.tuple (List.rev pats)) (Option.get body))

(* Type declaration handling *)
let derive_decl s get_f field_f record_f {ptype_kind; ptype_manifest; _} =
  (* let s =
   *   List.fold_left (fun acc ((_ct : core_type), _) -> acc) s ptype_params
   * in *)
  match ptype_kind with
  | Ptype_abstract -> Option.(join (map (get_f s) ptype_manifest))
  | Ptype_variant _ -> None
  | Ptype_record labs -> (
    try
      let field_f f =
        let field = get_f s f.pld_type |> Option.get in
        field_f field f.pld_name.txt
      in
      Some (record_f (List.map field_f labs))
    with Invalid_argument _ -> None )
  | Ptype_open -> None

let get_generator s =
  derive_decl s get_gen
    (fun gen name -> (lid_loc name, apply_nolbl gen [exp_id "rs"]))
    (fun fields ->
      let app = Exp.record fields None in
      lambda_s "rs" app)

let get_generator rs td =
  let rejection pred gen = apply_runtime "reject" [pred; gen] in
  match get_attribute_pstr "satisfying" td.ptype_attributes with
  | Some e -> (
    match Gegen.generate td e with
    | None -> Option.map (rejection e) (get_generator rs td)
    | x -> x )
  | None -> get_generator rs td

(* Given a rewritting state [rs] and and a type [t], search for the printer
   associated to [t] in [rs]. Returns a Parsetree.expression (corresponding
   to a printer) option. *)
let get_printer s =
  derive_decl s get_print
    (fun print name ->
      let field = apply_nolbl print [exp_id name] in
      let field_name = string_exp name in
      (string_concat ~sep:"=" [field_name; field], (lid_loc name, pat_s name)))
    (fun l ->
      let fields, pat = List.split l in
      let app = string_concat ~sep:"; " fields in
      let app = string_concat [string_exp "{"; app; string_exp "}"] in
      lambda (Pat.record pat Closed) app)

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

(* | Some e ->
 *     register_prop state (lparse t.ptype_name.txt)
 *       ( match get_property (Option.get t.ptype_manifest) state with
 *       | None -> e
 *       | Some e' -> compose_properties e e' ) *)

(* annotation handling *)
(***********************)
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
        let name = Format.asprintf "%s in %s" (bold_blue txt) (blue loc) in
        get_property ct state |> Option.to_list
        |> List.map (generate txt args name) )
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
