open Migrate_parsetree
open Ast_410
open Parsetree
open Ast_mapper
open Ast_helper
open Helper

(* number of generation per test *)
let count = ref 1000

let add_test args = apply_runtime "add_test" args |> Str.eval

let run = apply_runtime "run_test" [unit] |> Str.eval

(* QCheck test for constants *)
let test_constant (name : string) (f : expression) =
  let f = lambda (Pat.any ()) (apply_nolbl f [exp_id name]) in
  add_test [one; string_exp name; exp_id "QCheck.unit"; f]

(* generation of QCheck test *)
let test (name : string) (args : expression list) =
  add_test ([int_exp !count; string_exp name] @ args)

(* same as [pp], but in bold blue] *)
let bold_blue x = Format.asprintf "\x1b[34;1m%s\x1b[0m" x

(* same as [pp], but in blue *)
let blue x = Format.asprintf "\x1b[36m%s\x1b[0m" x

(* printer composition *)
let concat_printer p1 p2 =
  let p1_exp = apply_nolbl_s "fst" [exp_id "x"] in
  let p2_exp = apply_nolbl_s "snd" [exp_id "x"] in
  lambda_s "x"
    (string_concat
       [ string_exp "("
       ; string_concat ~sep:", "
           [apply_nolbl p1 [p1_exp]; apply_nolbl p2 [p2_exp]]
       ; string_exp ")" ])

(* builds an input from a list of generators and printers and apply to it the
   function funname *)
let generate inputs fn testname satisfy =
  let rec aux gen print pat args = function
    | [] -> (gen, print, pat, List.rev args)
    | (g, p) :: tl ->
        let name = get_name () in
        aux
          (apply_nolbl_s "QCheck.Gen.pair" [gen; g])
          (concat_printer print p)
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
type rewritting_state =
  { properties: expression Types.t
  ; generators: expression Types.t
  ; printers: expression Types.t }

let register_printer rs lid p =
  {rs with printers= Types.add lid p rs.printers}

let register_generator rs lid g =
  {rs with generators= Types.add lid g rs.generators}

let register_property rs lid p =
  {rs with properties= Types.add lid p rs.properties}

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

let get_gen_core_type rs =
  derive_core_type rs.generators (fun gens ->
      List.map (fun g -> apply_nolbl (Option.get g) [exp_id "x"]) gens
      |> Exp.tuple |> lambda_s "x")

let get_printer_core_type rs =
  derive_core_type rs.printers (fun printers ->
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
let rec get_property (t : core_type) (rs : rewritting_state) :
    expression option =
  match t.ptyp_desc with
  | Ptyp_constr ({txt; _}, []) -> Types.find_opt txt rs.properties
  | Ptyp_poly ([], ct) -> get_property ct rs
  | _ -> None

(* initial rewritting state, with a few generators/printers by default *)
let initial_rs =
  let add_id (t_id : string) (id : string) =
    Types.add (Longident.Lident t_id) (exp_id id)
  in
  (* TODO: add entries for int32, int64, nativeint, string, bytes, aliases
     Mod.t *)
  (* TODO: add entries for parametric types ref, list, array, option, lazy_t *)
  let generators =
    Types.empty
    |> add_id "unit" "QCheck.Gen.unit"
    |> add_id "bool" "QCheck.Gen.bool"
    |> add_id "char" "QCheck.Gen.char"
    |> add_id "int" "QCheck.Gen.int"
    |> add_id "float" "QCheck.Gen.float"
  in
  let printers =
    Types.empty
    |> add_id "unit" "QCheck.Print.unit"
    |> add_id "bool" "string_of_bool"
    |> add_id "char" "string_of_char"
    |> add_id "int" "string_of_int"
    |> add_id "float" "string_of_float"
  in
  {generators; printers; properties= Types.empty}

let derive s td =
  let id = lid td.ptype_name.txt in
  option_meet s (get_generator s td) (get_printer s td) (fun gen ->
      register_printer (register_generator s id gen) id)

(* update the rewritting state according to a type declaration *)
let declare_type state t =
  let state = derive state t in
  match get_attribute_pstr "satisfying" t.ptype_attributes with
  | None -> state
  | Some e -> register_property state (lid t.ptype_name.txt) e

(* annotation handling *)
(***********************)
let check_gen state pvb =
  match get_attribute_pstr "gen" pvb.pvb_attributes with
  | None -> state
  | Some {pexp_desc= Pexp_ident l; _} ->
      {state with generators= Types.add l.txt pvb.pvb_expr state.generators}
  | _ -> failwith "bad gen attribute"

let check_print state pvb =
  match get_attribute_pstr "print" pvb.pvb_attributes with
  | None -> state
  | Some {pexp_desc= Pexp_ident l; _} ->
      {state with printers= Types.add l.txt pvb.pvb_expr state.printers}
  | _ -> failwith "bad print attribute"

let get_infos state e =
  let helper state pat =
    match pat.ppat_desc with
    | Ppat_constraint (_, ({ptyp_desc= Ptyp_constr ({txt; _}, []); _} as ct))
      -> (
      try
        ( Some (Types.find txt state.generators)
        , Some (Types.find txt state.printers) )
      with Not_found ->
        (get_gen_core_type state ct, get_printer_core_type state ct) )
    | Ppat_constraint (_, ct) ->
        (get_gen_core_type state ct, get_printer_core_type state ct)
    | _ -> (None, None)
  in
  let rec aux state res = function
    | Pexp_fun (Nolabel, None, pat, exp) -> (
      match helper state pat with
      | Some g, Some p -> aux state ((g, p) :: res) exp.pexp_desc
      | _ -> raise Exit )
    | Pexp_constraint (_, ct) -> (state, List.rev res, ct)
    | _ -> raise Exit
  in
  try Some (aux state [] e) with Exit -> None

(* compute a list of tests to be added to the AST. handles: - explicitly
   typed constants - (fully) explicitly typed functions *)
let gather_tests state = function
  (* let constant:typ = val*)
  | { pvb_pat=
        { ppat_desc= Ppat_constraint ({ppat_desc= Ppat_var {txt; _}; _}, typ)
        ; _ }
    ; _ } ->
      get_property typ state
      |> Option.fold ~none:[] ~some:(fun p -> [test_constant txt p])
  (* let fn (arg1:typ1) (arg2:typ2) ... : return_typ = body *)
  | {pvb_pat= {ppat_desc= Ppat_var {txt; _}; _}; pvb_expr; pvb_loc; _} -> (
    match get_infos state pvb_expr.pexp_desc with
    | None -> []
    | Some (_, args, ct) ->
        let loc = Format.asprintf "%a" Location.print_loc pvb_loc in
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
          let tests = gather_tests state pvb in
          let state = check_gen state pvb in
          let state = check_print state pvb in
          let h' = mapper.structure_item mapper h in
          aux state (tests @ (h' :: res)) tl
      | h :: tl -> aux state (h :: res) tl
    in
    aux initial_rs [] str
  in
  {default_mapper with structure= handle_str}
