open Migrate_parsetree
open Ast_410
open Parsetree
open Ast_mapper
open Ast_helper
open Helper
open State

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
let test (name : string) (args : expression list) =
  letunit
    (open_runtime
       (apply_nolbl_s "add_fun" ([int_ !number; string_ name] @ args)))

(* call to set_seed *)
let gen_set_seed x = letunit (apply_runtime "set_seed" [int_ x])

(* call to run_test*)
let run () = letunit (apply_runtime "run_test" [unit])

let rejection pred gen = apply_nolbl_s "reject" [pred; gen]

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

let product typs =
  let open Info in
  let generator =
    try
      List.map
        (function
          | {generator= Some g; _} -> apply_nolbl g [exp_id "x"]
          | _ -> raise Exit)
        typs
      |> Exp.tuple |> lambda_s "x" |> Option.some
    with Exit -> None
  in
  let cardinality =
    try
      List.fold_left
        (fun acc -> function {cardinality= Some c; _} -> Z.mul acc c
          | _ -> raise Exit)
        Z.one typs
      |> Option.some
    with Exit -> None
  in
  let specification =
    let get_name = id_gen_gen () in
    let compose (pats, prop) p =
      match (prop, p.specification) with
      | x, None -> (Pat.any () :: pats, x)
      | None, Some p ->
          let name, id = get_name () in
          let app = apply_nolbl p [id] in
          (pat_s name :: pats, Some app)
      | Some p', Some p ->
          let name, id = get_name () in
          let app = apply_nolbl p' [id] in
          (pat_s name :: pats, Some (p &&@ app))
    in
    let pats, body = List.fold_left compose ([], None) typs in
    Option.map (lambda (Pat.tuple (List.rev pats))) body
  in
  let printer =
    let get_name = id_gen_gen () in
    let np = function
      | {printer= Some p; _} ->
          let n, id = get_name () in
          (apply_nolbl p [id], pat_s n)
      | {printer= None; _} -> raise Exit
    in
    try
      let names, pats = List.split (List.map np typs) in
      let b = string_concat ~sep:", " names in
      let b' = string_concat [string_ "("; b; string_ ")"] in
      lambda (Pat.tuple pats) b' |> Option.some
    with Exit -> None
  in
  Info.make printer generator specification cardinality

let derive_ctype (state : State.t) of_info ~tuple ~constrained =
  let rec aux ct =
    match get_attribute_pstr "satisfying" ct.ptyp_attributes with
    | Some e -> constrained ct e
    | None -> (
      match ct.ptyp_desc with
      | Ptyp_var s -> of_info (State.get (lparse s) state)
      | Ptyp_constr ({txt; _}, []) -> of_info (State.get txt state)
      | Ptyp_poly ([], ct) -> aux ct
      | Ptyp_tuple [] -> assert false
      | Ptyp_tuple [x] -> aux x
      | Ptyp_tuple tup -> tuple (List.map aux tup)
      | _ -> None )
  in
  aux

let default_printer = lambda_s "_" (string_ (gray "undefined"))

(* builds a n-tuple generator from a list of n generators *)
let gen_tuple gens =
  try
    List.map
      (function Some g -> apply_nolbl g [exp_id "x"] | None -> raise Exit)
      gens
    |> Exp.tuple |> lambda_s "x" |> Option.some
  with Exit -> None

(* builds a n-tuple printer from a list of n printers *)
let print_tuple p =
  let get_name = id_gen_gen () in
  let np = function
    | Some p ->
        let n, id = get_name () in
        (apply_nolbl p [id], pat_s n)
    | None -> raise Exit
  in
  try
    let names, pats = List.split (List.map np p) in
    let b = string_concat ~sep:", " names in
    let b' = string_concat [string_ "("; b; string_ ")"] in
    lambda (Pat.tuple pats) b' |> Option.some
  with Exit -> None

(* builds a n-tuple satisfying predicate from a list of n satisfying
   predicates *)
let sat_tuple p =
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
        (pat_s name :: pats, Some (p &&@ app))
  in
  let pats, body = List.fold_left compose ([], None) p in
  Option.map (lambda (Pat.tuple (List.rev pats))) body

let rec get_gen s =
  derive_ctype s
    (fun i -> Option.bind i Info.get_generator)
    ~tuple:gen_tuple
    ~constrained:(fun ct e ->
      match Gegen.solve_ct ct e with
      | None ->
          let rejection pred gen = apply_runtime "reject" [pred; gen] in
          Option.map (rejection e) (get_gen s {ct with ptyp_attributes= []})
      | x -> x)

let rec get_print s =
  derive_ctype s
    (fun i -> Option.bind i Info.get_printer)
    ~tuple:print_tuple
    ~constrained:(fun ct _ -> get_print s {ct with ptyp_attributes= []})

(*TODO: complete*)
let unify_patterns p p' =
  match (p.ppat_desc, p'.ppat_desc) with
  | Ppat_any, _ -> Some p'
  | _, Ppat_any -> Some p
  | Ppat_var s, Ppat_var s' -> if s.txt = s'.txt then Some p else None
  | _ -> None

let compose_properties p p' =
  match (p.pexp_desc, p'.pexp_desc) with
  | Pexp_fun (_, _, pat, expr), Pexp_fun (_, _, pat', expr') -> (
    match unify_patterns pat pat' with
    | None ->
        lambda_s "x"
          (apply_nolbl p [exp_id "x"] &&@ apply_nolbl p' [exp_id "x"])
    | Some pat ->
        let newexpr = expr &&@ expr' in
        let newp = lambda pat newexpr in
        lambda_s "x" (apply_nolbl newp [exp_id "x"]) )
  | _ ->
      lambda_s "x"
        (apply_nolbl p [exp_id "x"] &&@ apply_nolbl p' [exp_id "x"])

let rec get_prop s ct =
  derive_ctype s
    (fun i -> Option.bind i Info.get_specification)
    ~tuple:sat_tuple
    ~constrained:(fun ct p ->
      match get_prop s {ct with ptyp_attributes= []} with
      | None -> Some p
      | Some p' -> Some (compose_properties p p'))
    ct

(* generic derivation function for type declaration *)
let derive_decl (s : State.t) ~core_type ~field ~record ~constr ~sum ~sat
    ({ptype_kind; ptype_manifest; ptype_attributes; ptype_params; _} as td) =
  let field f =
    field (core_type s f.pld_type |> Option.get) f.pld_name.txt
  in
  let s =
    List.fold_left
      (fun s (ct, _var) -> State.register_param s ct)
      s ptype_params
  in
  let right =
    try
      match get_attribute_pstr "satisfying" ptype_attributes with
      | Some e -> sat td e
      | None -> (
        match ptype_kind with
        | Ptype_abstract -> Option.(join (map (core_type s) ptype_manifest))
        | Ptype_variant constructors ->
            let constr_f c =
              match c.pcd_args with
              | Pcstr_tuple ct ->
                  Some (constr (List.map (core_type s) ct) c.pcd_name)
              | Pcstr_record _labs -> None
            in
            sum (List.map constr_f constructors)
        | Ptype_record labs -> Some (record (List.map field labs))
        | Ptype_open -> None )
    with Invalid_argument _ -> None
  in
  match ptype_params with
  | [] -> right
  | (ct, _variance) :: t ->
      let func =
        List.fold_left
          (fun acc (t, _var) x -> acc (lambda_s (typ_var_of_ct t) x))
          (lambda_s (typ_var_of_ct ct))
          t
      in
      Option.map func right

let rec get_generator s =
  derive_decl s ~core_type:get_gen
    ~field:(fun gen name -> (lid_loc name, apply_nolbl gen [exp_id "rs"]))
    ~record:(fun fields -> Exp.record fields None |> lambda_s "rs")
    ~constr:(fun gs n ->
      match gs with
      | [] -> lambda_s "_" (Exp.construct (lid_loc n.txt) None)
      | [x] ->
          lambda_s "rs"
            (Exp.construct (lid_loc n.txt)
               (Some (apply_nolbl (Option.get x) [exp_id "rs"])))
      | l ->
          lambda_s "rs"
            (Exp.construct (lid_loc n.txt)
               (Some (apply_nolbl (gen_tuple l |> Option.get) [exp_id "rs"]))))
    ~sum:(fun gs ->
      Some (apply_nolbl_s "one_of" [list_of_list (List.map Option.get gs)]))
    ~sat:(fun td e ->
      match Gegen.solve_td td e with
      | None ->
          Option.map (rejection e)
            (get_generator s {td with ptype_attributes= []})
      | Some x -> x)

(* Given a rewritting state [rs] and and a type [t], search for the printer
   associated to [t] in [rs]. Returns a Parsetree.expression (corresponding
   to a printer) option. *)
let get_printer s td =
  let rec aux s td =
    derive_decl s ~core_type:get_print
      ~field:(fun print name ->
        let field = apply_nolbl print [exp_id name] in
        let field_name = string_ name in
        ( string_concat ~sep:"=" [field_name; field]
        , (lid_loc name, pat_s name) ))
      ~record:(fun l ->
        let fields, pat = List.split l in
        let app = string_concat ~sep:"; " fields in
        let app = string_concat [string_ "{"; app; string_ "}"] in
        lambda (Pat.record pat Closed) app)
      ~constr:(fun p n : case ->
        let constr pat = Pat.construct (lid_loc n.txt) pat in
        let id = id_gen_gen () in
        match p with
        | [] -> Exp.case (constr None) (string_ n.txt)
        | [print] ->
            let print = Option.value ~default:default_printer print in
            let p, e = id () in
            Exp.case
              (constr (Some (pat_s p)))
              (string_concat
                 [string_ (n.txt ^ "("); apply_nolbl print [e]; string_ ")"])
        | p ->
            let pat, exp =
              List.map
                (fun _ ->
                  let p, e = id () in
                  (pat_s p, e))
                p
              |> List.split
            in
            Exp.case
              (constr (Some (Pat.tuple pat)))
              (apply_nolbl (print_tuple p |> Option.get) [Exp.tuple exp]))
      ~sum:(fun (cl : case option list) ->
        Some
          (Exp.function_
             (List.map
                (Option.value
                   ~default:(Exp.case (Pat.any ()) default_printer))
                cl)))
      ~sat:(fun td _ -> aux s {td with ptype_attributes= []})
      td
  in
  aux s td |> Option.value ~default:default_printer

let rec get_property s =
  derive_decl s ~core_type:get_prop
    ~field:(fun prop name ->
      (apply_nolbl prop [exp_id name], (lid_loc name, pat_s name)))
    ~record:(fun l ->
      let fields, pat = List.split l in
      match fields with
      | h :: tl ->
          List.fold_left ( &&@ ) h tl |> lambda (Pat.record pat Closed)
      | _ -> (*record with 0 field*) assert false)
    ~constr:(fun p n : case ->
      let constr pat = Pat.construct (lid_loc n.txt) pat in
      match p with
      | [] -> Exp.case (constr None) true_
      | [prop] ->
          let prop = Option.get prop in
          let id = id_gen_gen () in
          let p, e = id () in
          Exp.case (constr (Some (pat_s p))) (apply_nolbl prop [e])
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
            (constr (Some (Pat.tuple pat)))
            (apply_nolbl (sat_tuple p |> Option.get) [Exp.tuple exp]))
    ~sum:(fun (cl : case option list) ->
      if List.for_all (( = ) None) cl then None
      else
        Some
          (Exp.function_
             (List.map
                (function
                  | None -> Exp.case (Pat.any ()) true_ | Some c -> c)
                cl)))
    ~sat:(fun td p ->
      let p' = get_property s {td with ptype_attributes= []} in
      match p' with
      | None -> Some p
      | Some p' -> Some (compose_properties p p'))

let get_generator s td =
  let gen = get_generator s td in
  let id = td.ptype_name.txt in
  ( match gen with
  | None -> Log.print "No generator derived for type %s\n%!" id
  | Some g ->
      Log.print "Registering a generator for type %s\n%a\n%!" id
        print_expression g ) ;
  gen

let get_property s td =
  let prop = get_property s td in
  let id = td.ptype_name.txt in
  ( match prop with
  | None -> Log.print "No constraint attached to type %s\n%!" id
  | Some g ->
      Log.print "Registering a constraint for type %s\n%a\n%!" id
        print_expression g ) ;
  prop

let derive (s : State.t) (td : type_declaration) =
  let infos = (get_generator s td, get_printer s td, get_property s td) in
  let id = lparse td.ptype_name.txt in
  State.update s id infos

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
  | Some {pexp_desc= Pexp_ident l; _} ->
      Log.print "setting %a as a generator for %a\n%!" print_pat vb.pvb_pat
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
  let get_gen_print pat =
    match pat.ppat_desc with
    | Ppat_construct ({txt= Lident "()"; _}, _) ->
        (* allow to omit the explicit type annotation for the unit type*)
        ( State.get_gen s (lparse "unit")
        , State.get_print s (lparse "unit")
        , "unit" )
    | Ppat_constraint (_, t) ->
        (get_gen s t, get_print s t, Format.asprintf "%a" print_coretype t)
    | _ ->
        ( None
        , None
        , Format.asprintf "missing type annotation for %a" print_pat pat )
  in
  let rec aux res = function
    | Pexp_fun (Nolabel, None, pat, exp) ->
        aux (get_gen_print pat :: res) exp.pexp_desc
    | Pexp_constraint (_, ct) -> (List.rev res, ct)
    | _ -> raise Exit
  in
  try
    let infos, ct = aux [] e in
    Some
      ( List.map
          (function Some g, Some p, _ -> (g, p) | _ -> raise Exit)
          infos
      , ct )
  with Exit -> None

(* compute a list of tests to be added to the AST. handles: explicitly typed
   constants and (fully) explicitly typed functions *)
let gather_tests vb state =
  let loc = Format.asprintf "%a" Location.print_loc vb.pvb_loc in
  match vb.pvb_pat.ppat_desc with
  (* let constant:typ = val*)
  | Ppat_constraint ({ppat_desc= Ppat_var {txt; _}; _}, typ) ->
      get_prop state typ
      |> Option.fold ~none:[] ~some:(fun p ->
             Log.print "Trying to generate a test for the constant %a\n"
               print_pat vb.pvb_pat ;
             [test_constant txt loc p])
  (* let fn (arg1:typ1) (arg2:typ2) ... : return_typ = body *)
  | Ppat_var {txt; _} -> (
    match get_infos state vb.pvb_expr.pexp_desc with
    | None -> []
    | Some (args, ct) -> (
        let p =
          get_print state ct |> Option.value ~default:default_printer
        in
        let name = Format.asprintf "%s in %s" (bold_blue txt) (blue loc) in
        let prop = get_prop state ct in
        match prop with
        | Some prop ->
            Log.print "Trying to generate a test for the function %a\n"
              print_pat vb.pvb_pat ;
            [generate txt args p name prop]
        | _ -> [] ) )
  | _ -> []

(* actual mapper *)
let mapper =
  let in_attribute = ref false in
  let handle_str mapper str =
    let rec aux res state = function
      | [] ->
          let tests =
            match !seed with None -> res | Some x -> gen_set_seed x :: res
          in
          List.rev (if !in_attribute then res else run () :: tests)
      (* type declaration *)
      | ({pstr_desc= Pstr_type (_, [t]); _} as h) :: tl ->
          aux (h :: res) (declare_type state t) tl
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
        let s, _, _ = Location.get_pos_info h.pstr_loc.loc_start in
        Log.set_output s ) ;
    aux [] State.s0 str
  in
  let handle_attr m a =
    (* deactivate test generation in attributes *)
    in_attribute := true ;
    let res = default_mapper.attribute m a in
    in_attribute := false ;
    res
  in
  {default_mapper with structure= handle_str; attribute= handle_attr}
