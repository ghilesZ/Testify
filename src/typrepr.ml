open Migrate_parsetree
open Ast_410
open Parsetree
open Helper
open Location

(** representation of an OCaml type *)

type t =
  { gen: expression option
  ; spec: expression option
  ; card: Card.t
  ; print: expression
  ; of_arbogen: expression option }

let print_expr fmt e =
  Format.fprintf fmt "\n```ocaml@.@[%a@]\n```" print_expression e

let print fmt {gen; spec; card; print; of_arbogen} =
  let print_opt f fmt = function
    | None -> Format.fprintf fmt " none"
    | Some e -> f fmt e
  in
  Format.fprintf fmt "- Cardinality: %a\n" Card.pp card ;
  Format.fprintf fmt "- Printer:%a\n" print_expr print ;
  Format.fprintf fmt "- Specification:%a\n" (print_opt print_expr) spec ;
  Format.fprintf fmt "- Generator: %a\n" (print_opt print_expr) gen ;
  Format.fprintf fmt "- Of_arbogen: %a\n" (print_opt print_expr) of_arbogen

let default_printer = lambda_s "_" (string_ "<...>")

let empty =
  { gen= None
  ; spec= None
  ; card= Unknown
  ; print= default_printer
  ; of_arbogen= None }

let add_printer info p = {info with print= p}

let add_generator info g = {info with gen= Some g}

let add_specification info s = {info with spec= Some s}

let free g c p of_arbogen =
  {print= p; gen= Some g; spec= None; card= c; of_arbogen}

let make print gen spec card of_arbogen = {gen; spec; card; print; of_arbogen}

let end_module name typ =
  { typ with
    gen= Option.map (let_open name) typ.gen
  ; spec= Option.map (let_open name) typ.spec
  ; print= let_open name typ.print }

(* Predefined types *)

let unit =
  free
    (exp_id "QCheck.Gen.unit")
    (Finite Z.one)
    (exp_id "QCheck.Print.unit")
    (Some (exp_id "arbogen_to_unit"))

let bool =
  free
    (exp_id "QCheck.Gen.bool")
    (Card.of_int 2) (exp_id "string_of_bool")
    (Some (exp_id "arbogen_to_bool"))

let char =
  free
    (exp_id "QCheck.Gen.char")
    (Card.of_int 256) (exp_id "string_of_char") None

let int =
  free (exp_id "QCheck.Gen.int")
    (Z.pow (Z.of_int 2) (Sys.int_size - 1) |> Card.finite)
    (exp_id "string_of_int")
    (Some (exp_id "arbogen_to_int"))

let float =
  free
    (exp_id "QCheck.Gen.float")
    (Z.pow (Z.of_int 2) 64 |> Card.finite)
    (exp_id "string_of_float")
    (Some (exp_id "arbogen_to_float"))

let param list = List.map (fun s -> (Typ.var s, Asttypes.Invariant)) list

let ptype ?manifest name params kind =
  { ptype_name= def_loc name
  ; ptype_params= List.map (fun s -> (Typ.var s, Asttypes.Invariant)) params
  ; ptype_cstrs= []
  ; ptype_kind= kind
  ; ptype_private= Asttypes.Public
  ; ptype_manifest= manifest
  ; ptype_attributes= []
  ; ptype_loc= Location.none }

(** {2 Polymorphic types} *)

type param = {vars: string list; body: type_declaration}

let option_ =
  let vars = ["a"] in
  let alpha = [Typ.var "a"] in
  let body =
    let none = Type.constructor_s "None" in
    let some = Type.constructor_s ~args:(Pcstr_tuple alpha) "Some" in
    let kind = Ptype_variant [none; some] in
    ptype
      ~manifest:(Typ.poly ["a"] (Typ.constr_s "option" alpha))
      "option" vars kind
  in
  {vars; body}

let ref_ =
  let vars = ["a"] in
  let alpha = Typ.var "a" in
  let body =
    let contents = Type.field_s ~mut:Mutable "contents" alpha in
    let kind = Ptype_record [contents] in
    ptype
      ~manifest:(Typ.poly ["a"] (Typ.constr_s "ref" [alpha]))
      "ref" vars kind
  in
  {vars; body}

let result_ =
  let vars = ["a"; "b"] in
  let alpha = Typ.var "a" in
  let beta = Typ.var "b" in
  let body =
    let ok = Type.constructor ~args:(Pcstr_tuple [alpha]) (def_loc "Ok") in
    let error =
      Type.constructor ~args:(Pcstr_tuple [beta]) (def_loc "Error")
    in
    let kind = Ptype_variant [ok; error] in
    ptype
      ~manifest:(Typ.poly ["a"; "b"] (Typ.constr_s "error" [alpha; beta]))
      "error" vars kind
  in
  {vars; body}

let list_ =
  let vars = ["a"] in
  let alpha = Typ.var "a" in
  let alpha_list = Typ.constr_s "list" [alpha] in
  let body =
    let cons =
      Type.constructor ~args:(Pcstr_tuple [alpha; alpha_list]) (def_loc "::")
    in
    let empty = Type.constructor (def_loc "[]") in
    let kind = Ptype_variant [cons; empty] in
    ptype
      ~manifest:(Typ.poly ["a"] (Typ.constr_s "list" [alpha]))
      "list" vars kind
  in
  {vars; body}

(** {2 Recursive types} *)

module Rec = struct
  let make typ_name =
    { print= exp_id ("print_" ^ typ_name)
    ; gen= Some (exp_id ("gen_" ^ typ_name))
    ; spec= Some (exp_id ("spec_" ^ typ_name))
    ; card= Infinite
    ; of_arbogen= Some (exp_id ("of_arbogen_" ^ typ_name)) }

  let make_mutually_rec header typs get_field =
    try
      let rec_def =
        List.map
          (fun (id, typ) -> (header ^ "_" ^ id, get_field typ |> Option.get))
          typs
        |> let_rec_and
      in
      List.map
        (fun (name, _) ->
          let func = Some (rec_def (exp_id (header ^ "_" ^ name))) in
          func )
        typs
    with Invalid_argument _ -> List.map (fun _ -> None) typs

  let finish typs =
    let printers =
      make_mutually_rec "print" typs (fun typ -> Some typ.print)
      |> List.map Option.get
    in
    let generators = make_mutually_rec "gen" typs (fun typ -> typ.gen) in
    let specs = make_mutually_rec "spec" typs (fun typ -> typ.spec) in
    let of_arbogen =
      make_mutually_rec "of_arbogen" typs (fun typ -> typ.of_arbogen)
    in
    List.map5
      (fun print gen spec (name, typ) of_arbogen ->
        (name, {typ with print; gen; spec; of_arbogen}) )
      printers generators specs typs of_arbogen
end

(** {2 Type composition} *)

(** tuples *)
module Product = struct
  let gen_body typs =
    List.map
      (function
        | {gen= Some g; _} -> apply_nolbl g [exp_id "rs"] | _ -> raise Exit
        )
      typs
    |> tuple

  let generator typs =
    try gen_body typs |> lambda_s "rs" |> Option.some with Exit -> None

  let specification typs =
    match typs with
    | [] -> assert false
    | _ when List.for_all (fun t -> t.spec = None) typs -> None
    | _ ->
        let get_name = id_gen_gen () in
        let compose (pats, body) p =
          match (body, p.spec) with
          | x, None -> (pat_s "_" :: pats, x)
          | None, Some p ->
              let name, id = get_name () in
              let app = apply_nolbl p [id] in
              (pat_s name :: pats, Some app)
          | Some p', Some p ->
              let name, id = get_name () in
              let app = apply_nolbl p [id] in
              (pat_s name :: pats, Some (p' &&@ app))
        in
        let pats, body = List.fold_left compose ([], None) typs in
        Option.map (lambda (pat_tuple (List.rev pats))) body

  let cardinality typs = List.map (fun t -> t.card) typs |> Card.product

  let printer typs =
    let get_name = id_gen_gen () in
    let np p =
      let n, id = get_name () in
      (apply_nolbl p.print [id], pat_s n)
    in
    let names, pats = List.split (List.map np typs) in
    let b = string_concat ~sep:", " names in
    let b' = string_concat [string_ "("; b; string_ ")"] in
    lambda (pat_tuple pats) b'

  let arbogen typs =
    try
      let get_name = id_gen_gen () in
      let np p =
        let n, id = get_name () in
        (apply_nolbl (p.of_arbogen |> Option.get) [id; exp_id "queue"], n)
      in
      let bodies, pats = List.split (List.map np typs) in
      List.fold_left2
        (fun acc p body ->
          let pat = pat_tuple [pat_s p; pat_s "queue"] in
          let_pat pat body acc )
        (tuple (List.map exp_id pats))
        (List.rev pats) (List.rev bodies)
      |> lambda_s "queue" |> Option.some
    with Invalid_argument _ -> None

  let make typs =
    make (printer typs) (generator typs) (specification typs)
      (cardinality typs) (arbogen typs)
end

(** ADTs *)
module Sum = struct
  let cardinality typs =
    typs |> List.map (fun (_, args) -> Product.cardinality args) |> Card.sum

  let constr_generator constr args =
    let constr = construct constr in
    match args with
    | [] -> lambda_s "_" (constr None) |> Option.some
    | [{gen= Some g; _}] ->
        lambda_s "rs" (constr (Some (apply_nolbl g [exp_id "rs"])))
        |> Option.some
    | [{gen= None; _}] -> raise Exit
    | l -> (
      try lambda_s "rs" (constr (Some (Product.gen_body l))) |> Option.some
      with Exit -> None )

  let generator (variants : (string * t list) list) totalcard =
    try
      let weight c =
        Q.div (Q.of_bigint c) (Q.of_bigint totalcard)
        |> Q.to_float |> Helper.float_
      in
      apply_nolbl_s "weighted"
        [ list_of_list
            (List.map
               (fun (constr, typs) ->
                 let card = Product.cardinality typs |> Card.as_z in
                 Helper.pair (weight card)
                   (constr_generator constr typs |> Option.get) )
               variants )
        ; exp_id "rs" ]
      |> lambda_s "rs" |> Option.some
    with Exit | Invalid_argument _ -> None

  let generator_one_of (variants : (string * t list) list) =
    try
      let t = List.length variants in
      let weight = 1. /. float_of_int t |> Helper.float_ in
      apply_nolbl_s "weighted"
        [ list_of_list
            (List.map
               (fun (constr, typs) ->
                 Helper.pair weight
                   (constr_generator constr typs |> Option.get) )
               variants )
        ; exp_id "rs" ]
      |> lambda_s "rs" |> Option.some
    with Exit | Invalid_argument _ -> None

  let constr_printer txt typs =
    let id = id_gen_gen () in
    let constr pat = pat_construct_s txt pat in
    match typs with
    | [] -> case (constr None) (string_ txt)
    | [{print; _}] ->
        let pat, expr = id () in
        case
          (constr (Some (pat_s pat)))
          (string_concat [string_ txt; apply_nolbl print [expr]])
    | p ->
        let pat, exp =
          List.map
            (fun _ ->
              let p, e = id () in
              (pat_s p, e) )
            p
          |> List.split
        in
        case
          (constr (Some (pat_tuple pat)))
          (string_concat
             [string_ txt; apply_nolbl (Product.printer p) [tuple exp]] )

  let printer variants =
    let cases =
      List.map (fun (constr, args) -> constr_printer constr args) variants
    in
    function_ cases

  let constr_spec txt args =
    let id = id_gen_gen () in
    let constr pat = pat_construct_s txt pat in
    match args with
    | [] -> (constr None, None)
    | [last] ->
        let prop = Option.get last.spec in
        let p, e = id () in
        let pat = constr (Some (pat_s p)) in
        (pat, case pat (apply_nolbl prop [e]) |> Option.some)
    | p ->
        let pat, exp =
          List.map
            (fun _ ->
              let p, e = id () in
              (pat_s p, e) )
            p
          |> List.split
        in
        let pat = pat_tuple pat in
        ( pat
        , Option.map
            (fun spec ->
              case (constr (Some pat)) (apply_nolbl spec [tuple exp]) )
            (Product.specification args) )

  let specification variants =
    try
      let cases = List.map (fun (c, a) -> constr_spec c a) variants in
      if List.for_all (fun (_, c) -> c = None) cases then None
      else
        Some
          (function_
             (List.map
                (function p, None -> case p true_ | _, Some c -> c)
                cases ) )
    with Exit | Invalid_argument _ -> None

  let constr_arbg name args =
    let id = id_gen_gen () in
    let constr pats =
      let pat_l = Helper.pat_list pats in
      pat_construct_s "Node" (Some (pat_tuple [pat_string name; pat_l]))
    in
    match args with
    | [] -> case (constr []) (tuple [construct name None; exp_id "queue"])
    | [x] ->
        let of_arbg = Option.get x.of_arbogen in
        let p, e = id () in
        let pat = constr [pat_s p] in
        case pat (apply_nolbl of_arbg [e])
    | p ->
        let pat, _exp =
          List.map
            (fun _ ->
              let p, e = id () in
              (pat_s p, e) )
            p
          |> List.split
        in
        let pat = pat |> constr in
        case pat (construct name (Some (Product.arbogen args |> Option.get)))

  let arbogen variants =
    try
      let cases = List.map (fun (c, a) -> constr_arbg c a) variants in
      Some (function_ cases)
    with Exit | Invalid_argument _ -> None

  let make variants =
    let print = printer variants in
    let card = cardinality variants in
    let gen =
      if Card.is_finite card then generator variants (Card.as_z card)
      else generator_one_of variants
    in
    let spec = specification variants in
    let of_arbogen = arbogen variants in
    make print gen spec card of_arbogen
end

module Record = struct
  (* TODO: *)
  let cardinality fields = fields |> List.map snd |> Product.cardinality

  let generator fields =
    let field (n, t) =
      (lid_loc n, apply_nolbl (t.gen |> Option.get) [exp_id "rs"])
    in
    record (List.map field fields) None |> lambda_s "rs" |> Option.some

  let printer fields =
    let field (n, t) =
      let field = apply_nolbl t.print [exp_id n] in
      let field_name = n ^ " = " in
      (field_name, field, (lid_loc n, pat_s n))
    in
    match fields with
    | [] -> assert false
    | h :: tl ->
        let n, rhd, pat = field h in
        let fields, pat =
          List.fold_left
            (fun (rhd, pat) f ->
              let n', rhd', pat' = field f in
              (rhd' :: string_ ("; " ^ n') :: rhd, pat' :: pat) )
            ([rhd; string_ ("{" ^ n)], [pat])
            tl
        in
        let app = string_concat (List.rev fields) in
        let app = string_concat [app; string_ "}"] in
        lambda (pat_record_closed (List.rev pat)) app

  let specification fields =
    let field (n, t) =
      (apply_nolbl (t.spec |> Option.get) [exp_id n], (lid_loc n, pat_s n))
    in
    try
      let fields = List.map field fields in
      let fields, pat = List.split fields in
      match fields with
      | h :: tl ->
          List.fold_left ( &&@ ) h tl
          |> lambda (pat_record_closed pat)
          |> Option.some
      | _ -> (*record with 0 field*) assert false
    with Invalid_argument _ -> None

  let arbogen _fields = None

  let make fields =
    let c = cardinality fields in
    let g = generator fields in
    let p = printer fields in
    let s = specification fields in
    let arbg = arbogen fields in
    make p g s c arbg
end

module Constrained = struct
  (*TODO: complete *)
  let rec unify_patterns p p' =
    match (p.ppat_desc, p'.ppat_desc) with
    | Ppat_any, _ -> Some p'
    | _, Ppat_any -> Some p
    | Ppat_var s, Ppat_var s' -> if s.txt = s'.txt then Some p else None
    | Ppat_tuple t, Ppat_tuple t' -> (
      try
        Some
          ( List.map2 (fun e1 e2 -> Option.get (unify_patterns e1 e2)) t t'
          |> pat_tuple )
      with Invalid_argument _ -> None )
    | Ppat_record (r1, c), Ppat_record (r2, _) -> (
      try
        Some
          (pat_record
             (List.map2
                (fun (l1, p1) (l2, p2) ->
                  if l1.txt = l2.txt then
                    (l1, Option.get (unify_patterns p1 p2))
                  else
                    Format.asprintf "label %a and %a not in same order"
                      print_longident l1.txt print_longident l2.txt
                    |> invalid_arg )
                r1 r2 )
             c )
      with Invalid_argument msg ->
        Format.eprintf "%s\n%!" msg ;
        None )
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

  let rejection pred gen = apply_nolbl_s "reject" [pred; gen]

  let global_constraints = ["alldiff"; "increasing"; "decreasing"]

  let is_global_constraint (c : expression) =
    match c.pexp_desc with
    | Pexp_ident id -> List.mem (lid_to_string id.txt) global_constraints
    | Pexp_fun (Nolabel, None, pat, body) -> (
      match (pat.ppat_desc, body.pexp_desc) with
      | ( Ppat_var arg
        , Pexp_apply
            ( {pexp_desc= Pexp_ident funname; _}
            , [(Nolabel, {pexp_desc= Pexp_ident arg'; _})] ) ) ->
          List.mem (lid_to_string funname.txt) global_constraints
          && arg.txt = lid_to_string arg'.txt
      | _ -> false )
    | _ -> false

  let make ct typ e =
    let spec =
      match typ.spec with Some p -> compose_properties p e | None -> e
    in
    let default =
      { typ with
        gen= Option.map (rejection e) typ.gen
      ; spec= Some spec
      ; card= Unknown }
    in
    match Gegen.solve_ct ct spec with
    | Some (gen, card) -> {default with gen= Some gen; card= Finite card}
    | _ -> default

  let make_td td typ e =
    let spec =
      match typ.spec with Some p -> compose_properties p e | None -> e
    in
    let default =
      { typ with
        gen= Option.map (rejection e) typ.gen
      ; spec= Some spec
      ; card= Unknown }
    in
    match Gegen.solve_td td e with
    | Some (gen, card) -> {default with gen= Some gen; card= Finite card}
    | _ -> default

  let make_td td typ e =
    if is_global_constraint e then typ else make_td td typ e
end

(* generators for function 'a -> 'b are synthetized using only the 'b
   generator, i.e : let fun_gen = fun _ -> gen_b (). Generators are memoized
   to behave as mathematical functions *)
module Arrow = struct
  let generator =
    Option.map (fun g ->
        lambda_s "rs"
          (apply_nolbl_s "memo" [lambda_s "_" (apply_nolbl g [exp_id "rs"])]) )

  let printer = lambda_s "_" (string_ "(_ -> _)")

  let make _input output =
    let g = generator output.gen in
    make printer g None Card.Unknown None
end
