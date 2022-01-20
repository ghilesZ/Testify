open Migrate_parsetree
open Ast_410
open Parsetree
open Helper
open Location

(** representation of an OCaml type *)

type t =
  { boltz_spec: string Arbogen.Grammar.expression option
  ; gen: expression option
  ; spec: expression option
  ; card: Card.t
  ; print: expression }

let print_expr fmt e =
  Format.fprintf fmt "\n```ocaml@.@[%a@]\n```" print_expression e

let print fmt {gen; spec; card; print; boltz_spec; _} =
  let print_opt f fmt = function
    | None -> Format.fprintf fmt " none"
    | Some e -> f fmt e
  in
  Format.fprintf fmt "- Cardinality: %a\n" Card.pp card ;
  Format.fprintf fmt "- Printer:%a\n" print_expr print ;
  Format.fprintf fmt "- Specification:%a\n" (print_opt print_expr) spec ;
  Format.fprintf fmt "- Generator: %a\n" (print_opt print_expr) gen ;
  Format.fprintf fmt "- Boltzmann specification:%a"
    (print_opt
       (Arbogen.Grammar.pp_expression ~pp_ref:Format.pp_print_string) )
    boltz_spec

let default_printer = lambda_s "_" (string_ "<...>")

let empty =
  { boltz_spec= None
  ; gen= None
  ; spec= None
  ; card= Unknown
  ; print= default_printer }

let add_printer info p = {info with print= p}

let add_generator info g = {info with gen= Some g}

let add_specification info s = {info with spec= Some s}

let free bs g c p =
  {boltz_spec= Some bs; print= p; gen= Some g; spec= None; card= c}

let make boltz_spec print gen spec card = {boltz_spec; gen; spec; card; print}

let end_module name typ =
  { typ with
    gen= Option.map (let_open name) typ.gen
  ; spec= Option.map (let_open name) typ.spec
  ; print= let_open name typ.print }

(* Predefined types *)

let unit =
  free (Arbogen.Grammar.Z 0)
    (exp_id "QCheck.Gen.unit")
    (Finite Z.one)
    (exp_id "QCheck.Print.unit")

let bool =
  free (Arbogen.Grammar.Z 0)
    (exp_id "QCheck.Gen.bool")
    (Card.of_int 2) (exp_id "string_of_bool")

let char =
  free (Arbogen.Grammar.Z 0)
    (exp_id "QCheck.Gen.char")
    (Card.of_int 256) (exp_id "string_of_char")

let int =
  free (Arbogen.Grammar.Z 0) (exp_id "QCheck.Gen.int")
    (Z.pow (Z.of_int 2) (Sys.int_size - 1) |> Card.finite)
    (exp_id "string_of_int")

let float =
  free (Arbogen.Grammar.Z 0)
    (exp_id "QCheck.Gen.float")
    (Z.pow (Z.of_int 2) 64 |> Card.finite)
    (exp_id "string_of_float")

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
    ; boltz_spec= Some (Arbogen.Grammar.Ref typ_name) }

  let make_generator typs =
    let loc = Location.none in
    let grammar =
      typs
      |> List.map (fun (name, typ) -> (name, Option.get typ.boltz_spec))
      |> Arbogen.Frontend.ParseTree.completion
      |> Arbogen.Frontend.ParseTree.to_grammar
    in
    let wg =
      Arbogen.Boltzmann.(
        WeightedGrammar.of_grammar (Oracle.Naive.make grammar) grammar)
    in
    fun name ->
      [%expr
        fun rs ->
          let sicstus_something _ = assert false in
          let of_arbogen _ _ = assert false in
          let module R = Randtools.OcamlRandom in
          let module AB = Arbogen.Boltzmann in
          Random.set_state rs ;
          let target = 30 in
          (* XXX. arbitrary size *)
          let max_try = 1_000_000 in
          let wg = [%e AGPrint.weighted_grammar wg] in
          match
            AB.search_seed
              (module R)
              wg ~size_min:target ~size_max:target ~max_try
          with
          | Some (_size, state) ->
              R.set_state state ;
              let tree, _ = AB.free_gen (module R) wg [%e string_ name] in
              let nb_collect =
                Arbogen.Tree.fold
                  (fun lab ->
                    List.fold_left ( + )
                      (if String.equal lab "@collect" then 1 else 0) )
                  tree
              in
              let vals = sicstus_something nb_collect in
              of_arbogen vals tree
          | None -> assert false]

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
    let generators =
      let make_gen = make_generator typs in
      List.map (fun (name, _) -> Some (make_gen name)) typs
    in
    let specs = make_mutually_rec "spec" typs (fun typ -> typ.spec) in
    List.map4
      (fun print gen spec (name, typ) -> (name, {typ with print; gen; spec}))
      printers generators specs typs
end

(** {2 Infinite types} *)

(** Functions specific to infinite types, regardless of their shape. *)
module Infinite = struct
  let generator name expr =
    let loc = Location.none in
    let grammar =
      let open Arbogen.Frontend.ParseTree in
      to_grammar (completion [(name, expr)])
    in
    let wg =
      let open Arbogen.Boltzmann in
      WeightedGrammar.of_grammar (Oracle.Naive.make grammar) grammar
    in
    [%expr
      fun rs ->
        let sicstus_something _ = assert false in
        let of_arbogen _ _ = assert false in
        let module R = Randtools.OcamlRandom in
        let module AB = Arbogen.Boltzmann in
        Random.set_state rs ;
        let target = 30 in
        (* XXX. arbitraty size *)
        let max_try = 1_000_000 in
        let wg = [%e AGPrint.weighted_grammar wg] in
        match
          AB.search_seed
            (module R)
            wg ~size_min:target ~size_max:target ~max_try
        with
        | Some (_size, state) ->
            R.set_state state ;
            let tree, _ = AB.free_gen (module R) wg in
            let nb_collect =
              Arbogen.Tree.fold
                (fun lab ->
                  List.fold_left ( + )
                    (if String.equal lab "@collect" then 1 else 0) )
                tree
            in
            let vals = sicstus_something nb_collect in
            of_arbogen vals tree
        | None -> assert false]
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

  let boltzmann_specification typs =
    try
      typs
      |> List.map (fun typ -> Option.get typ.boltz_spec)
      |> Arbogen.Grammar.product_n |> Option.some
    with Invalid_argument _ -> None

  let make typs =
    make
      (boltzmann_specification typs)
      (printer typs) (generator typs) (specification typs) (cardinality typs)
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

  let constr_printer txt typs =
    let id = id_gen_gen () in
    let constr pat = pat_construct (lid_loc txt) pat in
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

  let printer (variants : variants) =
    let cases =
      List.map
        (fun (constr, args) -> constr_printer constr (List.map fst args))
        variants
    in
    function_ cases

  let constr_spec txt args =
    let constr pat = pat_construct (lid_loc txt) pat in
    match args with
    | [] -> (constr None, None)
    | [(last, _)] ->
        let prop = Option.get last.spec in
        let id = id_gen_gen () in
        let p, e = id () in
        let pat = constr (Some (pat_s p)) in
        (pat, case pat (apply_nolbl prop [e]) |> Option.some)
    | p ->
        let id = id_gen_gen () in
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
            (args |> List.map fst |> Product.specification) )

  let specification (variants : variants) =
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

  let boltzmann_specification (variants : variants) =
    let variant_spec (_name, args) =
      match args with
      | [] -> Arbogen.Grammar.Z 1
      | _ ->
          args
          |> List.map (fun (t, collect) ->
                 (* XXX. This assumes that [@collect] occurs only on atomic types
               *)
                 if collect then Arbogen.Grammar.Ref "@collect"
                 else Option.get t.boltz_spec )
          |> Arbogen.Grammar.product_n
          |> Arbogen.Grammar.(product (Z 1))
    in
    try
      match List.map variant_spec variants with
      | [] ->
          Log.warn "What should we do with empty sum types?" ;
          None
      | es -> Some (Arbogen.Grammar.union_n es)
    with Invalid_argument _ -> None

  let make (name : string) (variants : variants) =
    let boltz_spec = boltzmann_specification variants in
    let print = printer variants in
    let card = cardinality variants in
    let gen =
      match card with
      | Infinite -> Option.map (Infinite.generator name) boltz_spec
      | Finite n -> generator variants n
      | Unknown -> None
    in
    let spec = specification variants in
    make boltz_spec print gen spec card
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

  let boltzmann_specification fields =
    fields |> List.map snd |> Product.boltzmann_specification

  let make fields =
    let c = cardinality fields in
    let g = generator fields in
    let p = printer fields in
    let s = specification fields in
    make (boltzmann_specification fields) p g s c
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
    let bs = None in
    let c = Card.Unknown in
    let g = generator output.gen in
    let p = printer in
    let s = None in
    make bs p g s c
end
