open Migrate_parsetree
open Ast_410
open Parsetree
open Ast_mapper
open Ast_helper
open Helper

(* number of generation per test *)
let count = ref 100000

let add_test args = apply_runtime "add_test" args |> Str.eval

let run = apply_runtime "run_test" [unit] |> Str.eval

(* same as [pp], but in bold blue] *)
let bold_blue x = Format.asprintf "\x1b[34;1m%s\x1b[0m" x

(* same as [pp], but in blue *)
let blue x = Format.asprintf "\x1b[36m%s\x1b[0m" x

(* QCheck test for constants *)
let test_constant (name : string) loc (f : expression) =
  let f = lambda (Pat.any ()) (apply_nolbl f [exp_id name]) in
  let name = Format.asprintf "%s in %s" (bold_blue name) (blue loc) in
  add_test [one; string_exp name; exp_id "QCheck.unit"; f]

(* generation of QCheck test *)
let test (name : string) (args : expression list) =
  add_test ([int_exp !count; string_exp name] @ args)

(* builds an input from a list of generators and printers and apply to it the
   function funname *)
let generate inputs fn testname satisfy =
  let rec aux gen print pat args = function
    | [] -> (gen, print, pat, List.rev args)
    | (g, p) :: tl ->
        let name = get_name () in
        aux
          (apply_nolbl_s "QCheck.Gen.pair" [gen; g])
          (apply_nolbl_s "QCheck.Print.pair" [print; p])
          (Pat.tuple [pat; pat_s name])
          (exp_id name :: args) tl
  in
  match inputs with
  | (g, p) :: tl ->
      let name = get_name () in
      let pat = pat_s name in
      let gen, print, pat, args = aux g p pat [exp_id name] tl in
      let f = lambda pat ((satisfy @@@ exp_id fn) args) in
      let testname = Format.asprintf "of %s\n" testname in
      test testname
        [apply_lab_nolab_s "QCheck.make" [("print", print)] [gen]; f]
  | [] -> assert false

(* Utilities for state rewritting *)
(**********************************)

(* main type, for rewritting state. keeps tracks of : - test properties
   attached to a type. - current generators and printers *)
type state =
  { props: expression Types.t
  ; gens: expression Types.t
  ; prints: expression Types.t }

let register_print s lid p = {s with prints= Types.add lid p s.prints}

let register_gen s lid g = {s with gens= Types.add lid g s.gens}

let register_prop s lid p = {s with props= Types.add lid p s.props}

let derive_core_type env compose =
  let rec aux ct =
    match ct.ptyp_desc with
    | Ptyp_constr ({txt; _}, []) -> Types.find_opt txt env
    | Ptyp_poly ([], ct) -> aux ct
    | Ptyp_tuple tup -> (
        let subtypes = List.map aux tup in
        try compose subtypes |> Option.some with Invalid_argument _ -> None )
    | _ -> None
  in
  aux

let get_gen_core_type s =
  derive_core_type s.gens (fun gens ->
      List.map (fun g -> apply_nolbl (Option.get g) [exp_id "x"]) gens
      |> Exp.tuple |> lambda_s "x")

let get_printer_core_type s =
  derive_core_type s.prints (fun printers ->
      let np p =
        let n = get_name () in
        (apply_nolbl (Option.get p) [exp_id n], pat_s n)
      in
      let names, pats = List.split (List.map np printers) in
      let b = string_concat ~sep:", " names in
      let b' = string_concat [string_exp "("; b; string_exp ")"] in
      lambda (Pat.tuple pats) b')

(* Given a rewritting state [rs] and and a type [t], search for the generator
   associated to [t] in [rs]. Returns a Parsetree.expression (corresponding
   to a Gen.t) option. *)
let get_generator rs t =
  match t.ptype_kind with
  | Ptype_abstract -> (
    match t.ptype_manifest with
    | None -> None
    | Some m -> get_gen_core_type rs m )
  | Ptype_variant _ -> None
  | Ptype_record labs -> (
    try
      let handle_field f =
        let gen = get_gen_core_type rs f.pld_type |> Option.get in
        (lid_loc f.pld_name.txt, apply_nolbl gen [exp_id "rs"])
      in
      let app = Exp.record (List.map handle_field labs) None in
      Some (lambda_s "rs" app)
    with Invalid_argument _ -> None )
  | Ptype_open -> None

let get_generator rs td =
  let rejection pred gen = apply_runtime "reject" [pred; gen] in
  match get_attribute_pstr "satisfying" td.ptype_attributes with
  | Some e -> (
    match Gegen.generate td e with
    | None -> Option.map (rejection e) (get_generator rs td)
    | x -> x )
  | None -> None

(* Given a rewritting state [rs] and and a type [t], search for the printer
   associated to [t] in [rs]. Returns a Parsetree.expression (corresponding
   to a printer) option. *)
let get_printer rs t =
  match t.ptype_kind with
  | Ptype_abstract -> (
    match t.ptype_manifest with
    | None -> None
    | Some m -> get_printer_core_type rs m )
  | Ptype_variant _ -> None
  | Ptype_record labs -> (
    try
      let handle_field f =
        let print = get_printer_core_type rs f.pld_type |> Option.get in
        let field = apply_nolbl print [exp_id f.pld_name.txt] in
        let field_name = string_exp f.pld_name.txt in
        string_concat ~sep:"=" [field_name; field]
      in
      let to_s f = f.pld_name.txt in
      let app = string_concat ~sep:"; " (List.map handle_field labs) in
      let app = string_concat [string_exp "{"; app; string_exp "}"] in
      let pat =
        List.map (fun l -> (lid_loc (to_s l), pat_s (to_s l))) labs
      in
      Some (lambda (Pat.record pat Closed) app)
    with Invalid_argument _ -> None )
  | Ptype_open -> None

(* gets the property attached to the type [t] in [rs] (or None) *)
let rec get_property (t : core_type) (s : state) : expression option =
  match t.ptyp_desc with
  | Ptyp_constr ({txt; _}, []) -> Types.find_opt txt s.props
  | Ptyp_poly ([], ct) -> get_property ct s
  | _ -> None

(* initial rewritting state, with a few generators/printers by default *)
let initial_rs =
  let add_id (t : string) (g : string) (p : string) (gens, prints) =
    (Types.add (lid t) (exp_id g) gens, Types.add (lid t) (exp_id p) prints)
  in
  (* TODO: add entries for int32, int64, nativeint, string, bytes, aliases
     Mod.t and parametric types ref, list, array, option, lazy_t *)
  let gens, prints =
    (Types.empty, Types.empty)
    |> add_id "unit" "QCheck.Gen.unit" "QCheck.Print.unit"
    |> add_id "bool" "QCheck.Gen.bool" "string_of_bool"
    |> add_id "char" "QCheck.Gen.char" "string_of_char"
    |> add_id "int" "QCheck.Gen.int" "string_of_int"
    |> add_id "float" "QCheck.Gen.float" "string_of_float"
  in
  {gens; prints; props= Types.empty}

let derive s td =
  let id = lid td.ptype_name.txt in
  option_meet s (get_generator s td) (get_printer s td) (fun gen ->
      register_print (register_gen s id gen) id)

(* update the rewritting state according to a type declaration *)
let declare_type state t =
  let state = derive state t in
  match get_attribute_pstr "satisfying" t.ptype_attributes with
  | None -> state
  | Some e -> register_prop state (lid t.ptype_name.txt) e

(* annotation handling *)
(***********************)
let check_gen vb (s : state) : state =
  match get_attribute_pstr "gen" vb.pvb_attributes with
  | None -> s
  | Some {pexp_desc= Pexp_ident l; _} -> register_gen s l.txt vb.pvb_expr
  | _ -> failwith "bad gen attribute"

let check_print vb (s : state) =
  match get_attribute_pstr "print" vb.pvb_attributes with
  | None -> s
  | Some {pexp_desc= Pexp_ident l; _} -> register_print s l.txt vb.pvb_expr
  | _ -> failwith "bad print attribute"

let get_infos (s : state) e =
  let helper pat =
    match pat.ppat_desc with
    | Ppat_constraint (_, t) ->
        (get_gen_core_type s t, get_printer_core_type s t)
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

(* compute a list of tests to be added to the AST. handles: - explicitly
   typed constants - (fully) explicitly typed functions *)
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
        get_property ct state
        |> Option.fold ~none:[] ~some:(fun p -> [generate args txt name p]) )
  | _ -> []

(* actual mapper *)
let mapper =
  let handle_str mapper str =
    let rec aux state res = function
      | [] -> List.rev (run :: res)
      | ({pstr_desc= Pstr_type (_, [t]); _} as h) :: tl ->
          aux (declare_type state t) (h :: res) tl
      | ({pstr_desc= Pstr_value (_, [pvb]); _} as h) :: tl ->
          let tests = gather_tests pvb state in
          let state = state |> check_gen pvb |> check_print pvb in
          let h' = mapper.structure_item mapper h in
          aux state (tests @ (h' :: res)) tl
      | h :: tl -> aux state (h :: res) tl
    in
    aux initial_rs [] str
  in
  {default_mapper with structure= handle_str}
