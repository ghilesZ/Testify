open Migrate_parsetree
open Ast_410
open Parsetree
open Helper
open Location

(** representation of an OCaml type *)

type t =
  { boltz: (Boltz.t, string) Result.t
  ; gen: expression option
  ; spec: expression option
  ; card: Card.t
  ; print: expression
  ; of_arbogen: expression option
  ; collector: expression option }

let print_expr fmt e =
  Format.fprintf fmt "\n```ocaml@.@[%a@]\n```" print_expression e

let print fmt {gen; spec; card; print; boltz; of_arbogen; collector} =
  let print_opt f fmt = function
    | None -> Format.fprintf fmt " none"
    | Some e -> f fmt e
  in
  let print_res f fmt = function
    | Ok x -> f fmt x
    | Error msg -> Format.fprintf fmt "Absent because: %s" msg
  in
  Format.fprintf fmt "- Cardinality: %a\n" Card.pp card ;
  Format.fprintf fmt "- Printer:%a\n" print_expr print ;
  Format.fprintf fmt "- Specification:%a\n" (print_opt print_expr) spec ;
  Format.fprintf fmt "- Boltzmann specification:\n%a\n"
    (print_res Boltz.markdown)
    boltz ;
  Format.fprintf fmt "- Of_arbogen: %a\n" (print_opt print_expr) of_arbogen ;
  Format.fprintf fmt "- Generator: %a\n" (print_opt print_expr) gen ;
  Format.fprintf fmt "- Collector: %a\n" (print_opt print_expr) collector

let default_printer = lambda_s "_" (string_ "<...>")

let empty =
  { boltz= Error "empty type"
  ; gen= None
  ; spec= None
  ; card= Unknown
  ; print= default_printer
  ; of_arbogen= None
  ; collector= None }

let add_printer info p = {info with print= p}

let add_generator info g = {info with gen= Some g}

let add_specification info s = {info with spec= Some s}

let free bs g c p of_arbogen col =
  { boltz= Ok bs
  ; print= p
  ; gen= Some g
  ; spec= None
  ; card= c
  ; of_arbogen
  ; collector= Some col }

let make boltz print gen spec card of_arbogen collector =
  {boltz; gen; spec; card; print; of_arbogen; collector}

let end_module name typ =
  { typ with
    gen= Option.map (let_open name) typ.gen
  ; spec= Option.map (let_open name) typ.spec
  ; print= let_open name typ.print
  ; of_arbogen= Option.map (let_open name) typ.of_arbogen
  ; collector= Option.map (let_open name) typ.collector }

(* Predefined types *)
let unit =
  free Boltz.epsilon
    (exp_id "QCheck.Gen.unit")
    (Finite Z.one)
    (exp_id "QCheck.Print.unit")
    (Some (exp_id "Arbg.to_unit"))
    (exp_id "Collect.unit")

let bool =
  free Boltz.epsilon
    (exp_id "QCheck.Gen.bool")
    (Card.of_int 2) (exp_id "string_of_bool")
    (Some (exp_id "Arbg.to_bool"))
    (exp_id "Collect.bool")

let char =
  free Boltz.epsilon
    (exp_id "QCheck.Gen.char")
    (Card.of_int 256) (exp_id "string_of_char") None (exp_id "Collect.char")

let int =
  free Boltz.epsilon (exp_id "QCheck.Gen.int")
    (Z.pow (Z.of_int 2) (Sys.int_size - 1) |> Card.finite)
    (exp_id "string_of_int")
    (Some (exp_id "Arbg.to_int"))
    (exp_id "Collect.int")

let float =
  free Boltz.epsilon
    (exp_id "QCheck.Gen.float")
    (Z.pow (Z.of_int 2) 64 |> Card.finite)
    (exp_id "string_of_float")
    (Some (exp_id "Arbg.to_float"))
    (exp_id "Collect.float")

let param list = List.map (fun s -> (Typ.var s, Asttypes.Invariant)) list

let ptype ?manifest name params kind =
  { ptype_name= def_loc name
  ; ptype_params= List.map (fun s -> (Typ.var s, Asttypes.Invariant)) params
  ; ptype_cstrs= []
  ; ptype_kind= kind
  ; ptype_private= Asttypes.Public
  ; ptype_manifest= manifest
  ; ptype_attributes= []
  ; ptype_loc= !current_loc }

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
    ; boltz= Ok (Boltz.ref typ_name)
    ; of_arbogen= Some (exp_id ("of_arbogen_" ^ typ_name))
    ; collector= Some (exp_id ("collect_" ^ typ_name)) }

  let make_generator typs =
    let grammar =
      typs
      |> List.map_result (fun (name, typ) ->
             Result.map (Boltz.as_grammar name) typ.boltz )
      |> Result.map List.flatten
    in
    let wg = Result.map Boltz.compile grammar in
    Result.map
      (fun wg name of_arbogen ->
        let loc = !current_loc in
        [%expr
          fun rs ->
            (* let sicstus_something _ = assert false in *)
            let sicstus_something n = List.init n Fun.id in
            let wg = [%e wg] in
            let tree = Arbg.generate wg [%e string_ name] rs in
            let nb_collect = Arbg.count_collect tree in
            let queue = sicstus_something nb_collect in
            fst ([%e of_arbogen] tree queue rs)] )
      wg

  let rec_def header get_field typs =
    List.map
      (fun (id, typ) -> (header ^ "_" ^ id, get_field typ |> Option.get))
      typs
    |> let_rec_and

  let make_mutually_rec header typs get_field =
    try
      List.map
        (fun (name, _) ->
          let func =
            Some
              (rec_def header get_field typs (exp_id (header ^ "_" ^ name)))
          in
          func )
        typs
    with Invalid_argument _ -> List.map (fun _ -> None) typs

  let finish typs =
    let printers =
      make_mutually_rec "print" typs (fun typ -> Some typ.print)
      |> List.map Option.get
    in
    let specs = make_mutually_rec "spec" typs (fun typ -> typ.spec) in
    let of_arbogen =
      make_mutually_rec "of_arbogen" typs (fun typ -> typ.of_arbogen)
    in
    let collector =
      make_mutually_rec "collector" typs (fun typ -> typ.collector)
    in
    let generators =
      Result.fold
        ~ok:(fun make_gen ->
          List.map
            (fun (name, t) ->
              try
                Option.map
                  (fun _arbg ->
                    let pre =
                      rec_def "of_arbogen" (fun typ -> typ.of_arbogen) typs
                    in
                    pre (make_gen name (exp_id ("of_arbogen_" ^ name))) )
                  t.of_arbogen
              with _ -> None )
            typs )
        ~error:(fun msg ->
          Log.warn "Unable to derive Boltzmann sampler: %s" msg ;
          List.map (fun _ -> None) typs )
        (make_generator typs)
    in
    List.map6
      (fun print gen spec (name, typ) of_arbogen collector ->
        (name, {typ with print; gen; spec; of_arbogen; collector}) )
      printers generators specs typs of_arbogen collector
end

(** {2 Infinite types} *)

(** Functions specific to infinite types, regardless of their shape. *)
module Infinite = struct
  let generator name boltz =
    let wg = Boltz.compile (Boltz.as_grammar name boltz) in
    let loc = !current_loc in
    [%expr
      fun rs ->
        let sicstus_something _ = assert false in
        let of_arbogen _ _ = assert false in
        let wg = [%e wg] in
        let tree = Arbg.generate wg [%e string_ name] rs in
        let nb_collect = Arbg.count_collect tree in
        let vals = sicstus_something nb_collect in
        fst (of_arbogen vals tree)]
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
          | x, None -> (Pat.of_string "_" :: pats, x)
          | None, Some p ->
              let name, id = get_name () in
              let app = apply_nolbl p [id] in
              (Pat.of_string name :: pats, Some app)
          | Some p', Some p ->
              let name, id = get_name () in
              let app = apply_nolbl p [id] in
              (Pat.of_string name :: pats, Some (p' &&@ app))
        in
        let pats, body = List.fold_left compose ([], None) typs in
        Option.map (lambda (Pat.tuple (List.rev pats))) body

  let cardinality typs = List.map (fun t -> t.card) typs |> Card.product

  let printer typs =
    let get_name = id_gen_gen () in
    let np p =
      let n, id = get_name () in
      (apply_nolbl p.print [id], Pat.of_string n)
    in
    let names, pats = List.split (List.map np typs) in
    let b = string_concat ~sep:", " names in
    let b' = string_concat [string_ "("; b; string_ ")"] in
    lambda (Pat.tuple pats) b'

  let arbogen_body typs =
    let get_name = id_gen_gen () in
    let np p =
      let n, id = get_name () in
      ( apply_nolbl
          (p.of_arbogen |> Option.get)
          [id; exp_id "queue"; exp_id "rs"]
      , n )
    in
    let bodies, pats = List.split (List.map np typs) in
    List.fold_left2
      (fun acc p body ->
        let pat = Pat.tuple [Pat.of_string p; Pat.of_string "queue"] in
        let_pat pat body acc )
      (pair (tuple (List.map exp_id pats)) (exp_id "queue"))
      (List.rev pats) (List.rev bodies)

  let arbogen typs =
    try
      let loc = !Helper.current_loc in
      let body = arbogen_body typs in
      Some [%expr fun queue rs -> [%e body]]
    with Invalid_argument _ -> None

  let boltzmann_specification typs =
    typs
    |> List.map_result (fun typ -> typ.boltz)
    |> Result.map Boltz.product

  let collector typs =
    let get_name = id_gen_gen () in
    let np = function
      | {collector= Some c; _} ->
          let n, id = get_name () in
          (apply_nolbl c [id], Pat.of_string n)
      | {collector= None; _} -> raise Exit
    in
    try
      let names, pats = List.split (List.map np typs) in
      let b = list_of_list names in
      lambda (Pat.tuple pats) (apply_nolbl_s "List.flatten" [b])
      |> Option.some
    with Exit -> None

  let make typs : t =
    make
      (boltzmann_specification typs)
      (printer typs) (generator typs) (specification typs) (cardinality typs)
      (arbogen typs) (collector typs)
end

(** ADTs *)
module Sum = struct
  type variants = (string * (t * bool) list) list

  let cardinality : variants -> Card.t =
    let rec sum acc = function
      | [] -> Card.finite acc
      | (_, args) :: variants -> (
        match args |> List.map fst |> Product.cardinality with
        | Finite n -> sum (Z.add acc n) variants
        | (Infinite | Unknown) as c -> c )
    in
    sum Z.zero

  let constr_generator constr args =
    let constr = construct constr in
    match args with
    | [] -> lambda_s "_" (constr None) |> Option.some
    | [({gen= Some g; _}, _)] ->
        lambda_s "rs" (constr (Some (apply_nolbl g [exp_id "rs"])))
        |> Option.some
    | [({gen= None; _}, _)] -> raise Exit
    | l -> (
      try
        lambda_s "rs" (constr (Some (l |> List.map fst |> Product.gen_body)))
        |> Option.some
      with Exit -> None )

  let generator (variants : variants) totalcard =
    try
      let weight c =
        Q.div (Q.of_bigint c) (Q.of_bigint totalcard)
        |> Q.to_float |> Helper.float_
      in
      apply_nolbl_s "weighted"
        [ list_of_list
            (List.map
               (fun (constr, typs) ->
                 let card =
                   typs |> List.map fst |> Product.cardinality |> Card.as_z
                 in
                 Helper.pair (weight card)
                   (constr_generator constr typs |> Option.get) )
               variants )
        ; exp_id "rs" ]
      |> lambda_s "rs" |> Option.some
    with Exit | Invalid_argument _ -> None

  let pat_exp p id =
    List.map
      (fun _ ->
        let p, e = id () in
        (Pat.of_string p, e) )
      p
    |> List.split

  let constr_printer txt typs =
    let id = id_gen_gen () in
    let constr pat = Pat.construct_s txt pat in
    match typs with
    | [] -> case (constr None) (string_ txt)
    | [{print; _}] ->
        let pat, expr = id () in
        case
          (constr (Some (Pat.of_string pat)))
          (string_concat [string_ txt; apply_nolbl print [expr]])
    | p ->
        let pat, exp = pat_exp p id in
        case
          (constr (Some (Pat.tuple pat)))
          (string_concat
             [string_ txt; apply_nolbl (Product.printer p) [tuple exp]] )

  let printer (variants : variants) =
    let cases =
      List.map
        (fun (constr, args) -> constr_printer constr (List.map fst args))
        variants
    in
    function_ cases

  let constr_spec txt args =
    let id = id_gen_gen () in
    let constr pat = Pat.construct_s txt pat in
    match args with
    | [] -> (constr None, None)
    | [last] ->
        let prop = Option.get last.spec in
        let p, e = id () in
        let pat = constr (Some (Pat.of_string p)) in
        (pat, case pat (apply_nolbl prop [e]) |> Option.some)
    | p ->
        let pat, exp = pat_exp p id in
        let pat = Pat.tuple pat in
        ( pat
        , Option.map
            (fun spec ->
              case (constr (Some pat)) (apply_nolbl spec [tuple exp]) )
            (args |> Product.specification) )

  let specification (variants : variants) =
    try
      let cases =
        List.map (fun (c, a) -> constr_spec c (List.map fst a)) variants
      in
      if List.for_all (fun (_, c) -> c = None) cases then None
      else
        Some
          (function_
             (List.map
                (function p, None -> case p true_ | _, Some c -> c)
                cases ) )
    with Exit | Invalid_argument _ -> None

  let boltzmann_specification (variants : variants) =
    let variant_spec (name, args) =
      let args_spec =
        match args with
        | [] -> Ok Boltz.epsilon
        | _ ->
            args
            |> List.map_result (fun (t, collect) ->
                   (* XXX. This assumes that [@collect] occurs only on atomic types *)
                   if collect then Ok (Boltz.ref "@collect") else t.boltz )
            |> Result.map Boltz.product
      in
      Result.map
        (fun args_spec -> Boltz.(product [z; indirection name args_spec]))
        args_spec
    in
    match List.map_result variant_spec variants with
    | Ok [] -> Result.error "Empty sum type"
    | Ok es -> Ok (Boltz.union es)
    | Error _ as err -> err

  let constr_arbg name args =
    let id = id_gen_gen () in
    let loc = !Helper.current_loc in
    let constr pats =
      [%pat? Arbogen.Tree.Label ([%p Pat.string name], [%p Pat.list pats])]
    in
    match args with
    | [] -> case (constr []) [%expr [%e construct name None], queue]
    | [(x, _collect)] ->
        let of_arbg = Option.get x.of_arbogen in
        case
          (constr [[%pat? x1]])
          [%expr
            let x1', queue' = [%e of_arbg] x1 queue rs in
            [%e construct name (Some [%expr x1'])]]
    | p ->
        let pat, exp = pat_exp (List.map fst p) id in
        let pat_c = constr pat in
        let body =
          [%expr
            let [%p Pat.tuple pat], queue =
              [%e Product.arbogen (List.map fst args) |> Option.get] queue rs
            in
            ([%e construct name (Some (tuple exp))], queue)]
        in
        case pat_c body

  let arbogen name variants =
    let loc = !Helper.current_loc in
    try
      let cases = List.map (fun (c, a) -> constr_arbg c a) variants in
      let default =
        case [%pat? _] [%expr failwith "Ill-formed arbogen tree"]
      in
      Some
        [%expr
          fun arbg queue rs ->
            match arbg with
            | Arbogen.Tree.Label ([%p Pat.string name], [Tuple []; child]) ->
                [%e match_ [%expr child] (cases @ [default])]
            | _ -> failwith "Ill-formed arbogen tree"]
    with Exit | Invalid_argument _ -> None

  let constr_collect name args =
    let id = id_gen_gen () in
    match args with
    | [] -> case (Pat.construct_s name None) empty_list_exp
    | [x] ->
        let col = Option.get x.collector in
        let p, e = id () in
        let pat = Pat.construct_s name (Some (Pat.of_string p)) in
        case pat (apply_nolbl col [e])
    | p ->
        let pat, exp = pat_exp p id in
        let tup =
          apply_nolbl (Product.collector args |> Option.get) [tuple exp]
        in
        case (Pat.construct_s name (Some (Pat.tuple pat))) tup

  let collector variants =
    try
      let cases =
        List.map (fun (c, a) -> constr_collect c (List.map fst a)) variants
      in
      Some (function_ cases)
    with Exit | Invalid_argument _ -> None

  let make name variants : t =
    let print = printer variants in
    let card = cardinality variants in
    let boltz = boltzmann_specification variants in
    let gen =
      match card with
      | Infinite ->
          Result.fold
            ~ok:(Infinite.generator name >>> Option.some)
            ~error:(fun _ -> None)
            boltz
      | Finite n -> generator variants n
      | Unknown -> None
    in
    let spec = specification variants in
    let of_arbogen = arbogen name variants in
    make boltz print gen spec card of_arbogen (collector variants)
end

module Record = struct
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
      (field_name, field, (lid_loc n, Pat.of_string n))
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
        lambda (Pat.record_closed (List.rev pat)) app

  let specification fields =
    let field (n, t) =
      ( apply_nolbl (t.spec |> Option.get) [exp_id n]
      , (lid_loc n, Pat.of_string n) )
    in
    try
      let fields = List.map field fields in
      let fields, pat = List.split fields in
      match fields with
      | h :: tl ->
          List.fold_left ( &&@ ) h tl
          |> lambda (Pat.record_closed pat)
          |> Option.some
      | _ -> (*record with 0 field*) assert false
    with Invalid_argument _ -> None

  let boltzmann_specification fields =
    fields |> List.map snd |> Product.boltzmann_specification

  let arbogen fields =
    try
      let get_name = id_gen_gen () in
      let np (field, p) =
        let _, id = get_name () in
        ( lid_loc field
        , apply_nolbl
            (p.of_arbogen |> Option.get)
            [id; exp_id "queue"; exp_id "rs"] )
      in
      let f = List.map np fields in
      record f None |> lambda_s "queue" |> lambda_s "rs" |> Option.some
    with Invalid_argument _ -> None

  let make fields =
    let c = cardinality fields in
    let g = generator fields in
    let p = printer fields in
    let s = specification fields in
    let arbg = None in
    make (boltzmann_specification fields) p g s c arbg None
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
          |> Pat.tuple )
      with Invalid_argument _ -> None )
    | Ppat_record (r1, c), Ppat_record (r2, _) -> (
      try
        Some
          (Pat.record
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

  let global_constraints =
    [ "alldiff"
    ; "increasing"
    ; "decreasing"
    ; "increasing_strict"
    ; "decreasing_strict" ]

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
    if is_global_constraint e then
      if Card.is_finite typ.card then
        failwith "global constraints only allowed on recursive types"
      else typ
    else make_td td typ e
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
    let bs = Result.error "Arrow types not supported" in
    let c = Card.Unknown in
    let g = generator output.gen in
    make bs printer g None c None None
end
