open Migrate_parsetree
open Ast_410
open Parsetree
open Helper
open Ast_helper
open Location

(** representation of an OCaml type *)

module Card = struct
  type t = Unknown | Infinite | Finite of Z.t

  (** {3 Shorthands to build values} *)

  let finite (n : Z.t) = Finite n

  let of_int n = finite (Z.of_int n)

  (** {3 Shorthands to access values} *)

  let as_z = function
    | Finite n -> n
    | Infinite | Unknown -> invalid_arg "Card.as_z"

  (** {3 Pretty printing} *)

  let pp fmt = function
    | Unknown -> Format.pp_print_string fmt "unknown"
    | Infinite -> Format.pp_print_string fmt "infinite"
    | Finite n -> Helper.print_bigint fmt n
end

type t =
  { gen: expression option
  ; spec: expression option
  ; card: Card.t
  ; print: expression option
  ; collector: expression option }

let print_expr fmt e =
  Format.fprintf fmt "\n```ocaml@.@[%a@]\n```" print_expression e

let print fmt {gen; spec; card; print; _} =
  let print_opt f fmt = function
    | None -> Format.fprintf fmt " none"
    | Some e -> f fmt e
  in
  Format.fprintf fmt "- Cardinality: %a\n" Card.pp card ;
  Format.fprintf fmt "- Printer:%a\n" (print_opt print_expr) print ;
  Format.fprintf fmt "- Specification:%a\n" (print_opt print_expr) spec ;
  Format.fprintf fmt "- Generator: %a\n" (print_opt print_expr) gen
(* ; * Format.fprintf fmt "- Co-Collector: %a\n" (print_opt print_expr)
   collector *)

let empty =
  {gen= None; spec= None; card= Unknown; print= None; collector= None}

let add_printer info p = {info with print= Some p}

let add_generator info g = {info with gen= Some g}

let add_specification info s = {info with spec= Some s}

let free g c p col =
  {print= Some p; gen= Some g; spec= None; card= c; collector= Some col}

let make print gen spec card collector = {gen; spec; card; print; collector}

let make_rec typ_name =
  { print= Some (exp_id ("print_" ^ typ_name))
  ; gen= Some (exp_id ("gen_" ^ typ_name))
  ; spec= Some (exp_id ("spec_" ^ typ_name))
  ; collector= Some (exp_id ("collect_" ^ typ_name))
  ; card= Infinite }

let finish_rec name typ =
  let header fn field =
    Option.map
      (fun body ->
        let exp = letrec (fn ^ "_" ^ name) body (exp_id (fn ^ "_" ^ name)) in
        exp )
      field
  in
  { print= header "print" typ.print
  ; gen= header "gen" typ.gen
  ; spec= header "spec" typ.spec
  ; collector= header "collect" typ.collector
  ; card= Infinite }

let end_module name typ =
  { typ with
    gen= Option.map (let_open name) typ.gen
  ; spec= Option.map (let_open name) typ.spec
  ; print= Option.map (let_open name) typ.print
  ; collector= Option.map (let_open name) typ.collector }

(* Predefined types *)

let unit =
  free
    (exp_id "QCheck.Gen.unit")
    (Finite Z.one)
    (exp_id "QCheck.Print.unit")
    (exp_id "Collect.unit")

let bool =
  free
    (exp_id "QCheck.Gen.bool")
    (Card.of_int 2) (exp_id "string_of_bool") (exp_id "Collect.bool")

let char =
  free
    (exp_id "QCheck.Gen.char")
    (Card.of_int 256) (exp_id "string_of_char") (exp_id "Collect.char")

let int =
  free (exp_id "QCheck.Gen.int")
    (Z.pow (Z.of_int 2) (Sys.int_size - 1) |> Card.finite)
    (exp_id "string_of_int") (exp_id "Collect.int")

let float =
  free
    (exp_id "QCheck.Gen.float")
    (Z.pow (Z.of_int 2) 64 |> Card.finite)
    (exp_id "string_of_float")
    (exp_id "Collect.float")

let param list = List.map (fun s -> (Typ.var s, Asttypes.Invariant)) list

let ptype ?manifest name params kind =
  { ptype_name= none_loc name
  ; ptype_params= List.map (fun s -> (Typ.var s, Asttypes.Invariant)) params
  ; ptype_cstrs= []
  ; ptype_kind= kind
  ; ptype_private= Asttypes.Public
  ; ptype_manifest= manifest
  ; ptype_attributes= []
  ; ptype_loc= Location.none }

(** {1 Polymorphic types} *)

type param = {vars: string list; body: type_declaration}

let option_ =
  let vars = ["a"] in
  let alpha = [Typ.var "a"] in
  let body =
    let none = Type.constructor (none_loc "None") in
    let some =
      Type.constructor ~args:(Pcstr_tuple alpha) (none_loc "Some")
    in
    let kind = Ptype_variant [none; some] in
    ptype
      ~manifest:
        (Typ.poly [none_loc "a"] (Typ.constr (lid_loc "option") alpha))
      "option" vars kind
  in
  {vars; body}

let ref_ =
  let vars = ["a"] in
  let alpha = Typ.var "a" in
  let body =
    let contents = Type.field ~mut:Mutable (none_loc "contents") alpha in
    let kind = Ptype_record [contents] in
    ptype
      ~manifest:
        (Typ.poly [none_loc "a"] (Typ.constr (lid_loc "ref") [alpha]))
      "ref" vars kind
  in
  {vars; body}

let result_ =
  let vars = ["a"; "b"] in
  let alpha = Typ.var "a" in
  let beta = Typ.var "b" in
  let body =
    let ok = Type.constructor ~args:(Pcstr_tuple [alpha]) (none_loc "Ok") in
    let error =
      Type.constructor ~args:(Pcstr_tuple [beta]) (none_loc "Error")
    in
    let kind = Ptype_variant [ok; error] in
    ptype
      ~manifest:
        (Typ.poly
           [none_loc "a"; none_loc "b"]
           (Typ.constr (lid_loc "error") [alpha; beta]) )
      "error" vars kind
  in
  {vars; body}

(** {1 Type composition} *)

(** tuples *)
module Product = struct
  let gen_body typs =
    List.map
      (function
        | {gen= Some g; _} -> apply_nolbl g [exp_id "rs"] | _ -> raise Exit
        )
      typs
    |> Exp.tuple

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
          | x, None -> (Pat.any () :: pats, x)
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
        Option.map (lambda (Pat.tuple (List.rev pats))) body

  let cardinality =
    let rec prod acc = function
      | [] -> Card.finite acc
      | {card= Finite n; _} :: typs -> prod (Z.mul n acc) typs
      | {card= Infinite; _} :: _ ->
          Infinite (* XXX. Assumes that no type has cardinality zero. *)
      | {card= Unknown; _} :: _ -> Unknown
    in
    prod Z.one

  let printer typs =
    let get_name = id_gen_gen () in
    let np = function
      | {print= Some p; _} ->
          let n, id = get_name () in
          (apply_nolbl p [id], pat_s n)
      | {print= None; _} -> raise Exit
    in
    try
      let names, pats = List.split (List.map np typs) in
      let b = string_concat ~sep:", " names in
      let b' = string_concat [string_ "("; b; string_ ")"] in
      lambda (Pat.tuple pats) b' |> Option.some
    with Exit -> None

  let collector typs =
    let get_name = id_gen_gen () in
    let np = function
      | {collector= Some c; _} ->
          let n, id = get_name () in
          (apply_nolbl c [id], pat_s n)
      | {collector= None; _} -> raise Exit
    in
    try
      let names, pats = List.split (List.map np typs) in
      let b = list_of_list names in
      lambda (Pat.tuple pats) (apply_nolbl_s "List.flatten" [b])
      |> Option.some
    with Exit -> None

  let make typs =
    make (printer typs) (generator typs) (specification typs)
      (cardinality typs) (collector typs)
end

(** ADTs *)
module Sum = struct
  let cardinality =
    let rec sum acc = function
      | [] -> Card.finite acc
      | (_, args) :: variants ->
        begin match Product.cardinality args with
        | Finite n -> sum (Z.add acc n) variants
        | (Infinite | Unknown) as c -> c
        end
    in
    sum Z.zero

  let constr_generator constr args =
    let constr = Exp.construct (lid_loc constr.txt) in
    match args with
    | [] -> lambda_s "_" (constr None) |> Option.some
    | [{gen= Some g; _}] ->
        lambda_s "rs" (constr (Some (apply_nolbl g [exp_id "rs"])))
        |> Option.some
    | [{gen= None; _}] -> raise Exit
    | l -> (
      try lambda_s "rs" (constr (Some (Product.gen_body l))) |> Option.some
      with Exit -> None )

  let generator (variants : (string with_loc * t list) list) totalcard =
    try
      let weight =
        match totalcard with
        | Some t ->
            fun c ->
              Q.div (Q.of_bigint c) (Q.of_bigint t)
              |> Q.to_float |> Helper.float_
        | _ -> raise Exit
      in
      apply_nolbl_s "weighted"
        [ list_of_list
            (List.map
               (fun (constr, typs) ->
                 let card = Product.cardinality typs |> Card.as_z in
                 Helper.pair (weight card)
                   (constr_generator constr typs |> Option.get) )
               variants ) ]
      |> Option.some
    with Exit | Invalid_argument _ -> None

  let generator_one_of (variants : (string with_loc * t list) list) =
    try
      let t = List.length variants in
      let weight = 1. /. float_of_int t |> Helper.float_ in
      apply_nolbl_s "weighted"
        [ list_of_list
            (List.map
               (fun (constr, typs) ->
                 Helper.pair weight
                   (constr_generator constr typs |> Option.get) )
               variants ) ]
      |> Option.some
    with Exit | Invalid_argument _ -> None

  let constr_printer {txt; _} typs =
    let id = id_gen_gen () in
    let constr pat = Pat.construct (lid_loc txt) pat in
    match typs with
    | [] -> Exp.case (constr None) (string_ txt) |> Option.some
    | [{print= Some p; _}] ->
        let pat, expr = id () in
        Exp.case
          (constr (Some (pat_s pat)))
          (string_concat [string_ txt; apply_nolbl p [expr]])
        |> Option.some
    | [{print= None; _}] -> None
    | p ->
        let pat, exp =
          List.map
            (fun _ ->
              let p, e = id () in
              (pat_s p, e) )
            p
          |> List.split
        in
        Option.map
          (fun print ->
            Exp.case
              (constr (Some (Pat.tuple pat)))
              (string_concat
                 [string_ txt; apply_nolbl print [Exp.tuple exp]] ) )
          (Product.printer p)

  let printer variants =
    let cases =
      List.map (fun (constr, args) -> constr_printer constr args) variants
    in
    try Some (Exp.function_ (List.map Option.get cases))
    with Exit | Invalid_argument _ -> None

  let constr_spec {txt; _} args =
    let constr pat = Pat.construct (lid_loc txt) pat in
    match args with
    | [] -> (constr None, None)
    | [last] ->
        let prop = Option.get last.spec in
        let id = id_gen_gen () in
        let p, e = id () in
        let pat = constr (Some (pat_s p)) in
        (pat, Exp.case pat (apply_nolbl prop [e]) |> Option.some)
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
        let pat = Pat.tuple pat in
        ( pat
        , Option.map
            (fun spec ->
              Exp.case (constr (Some pat)) (apply_nolbl spec [Exp.tuple exp])
              )
            (Product.specification args) )

  let constr_collect {txt; _} args =
    let constr pat = Pat.construct (lid_loc txt) pat in
    match args with
    | [] -> (constr None, None)
    | [last] ->
        let prop = Option.get last.collector in
        let id = id_gen_gen () in
        let p, e = id () in
        let pat = constr (Some (pat_s p)) in
        (pat, Exp.case pat (apply_nolbl prop [e]) |> Option.some)
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
        let pat = Pat.tuple pat in
        ( pat
        , Option.map
            (fun col ->
              Exp.case (constr (Some pat)) (apply_nolbl col [Exp.tuple exp])
              )
            (Product.collector args) )

  let specification variants =
    try
      let cases = List.map (fun (c, a) -> constr_spec c a) variants in
      if List.for_all (fun (_, c) -> c = None) cases then None
      else
        Some
          (Exp.function_
             (List.map
                (function p, None -> Exp.case p true_ | _, Some c -> c)
                cases ) )
    with Exit | Invalid_argument _ -> None

  let collector variants =
    try
      let cases = List.map (fun (c, a) -> constr_collect c a) variants in
      if List.for_all (fun (_, c) -> c = None) cases then None
      else
        Some
          (Exp.function_
             (List.map
                (function
                  | p, None -> Exp.case p empty_list_exp | _, Some c -> c )
                cases ) )
    with Exit | Invalid_argument _ -> None

  let make variants =
    let print = printer variants in
    let card = cardinality variants in
    let gen = generator_one_of variants in
    let spec = specification variants in
    let col = collector variants in
    make print gen spec card col
end

module Record = struct
  (* TODO: *)
  let cardinality fields =
    fields |> List.map snd |> Product.cardinality

  let generator fields =
    let field (n, t) =
      (lid_loc n, apply_nolbl (t.gen |> Option.get) [exp_id "rs"])
    in
    Exp.record (List.map field fields) None |> lambda_s "rs" |> Option.some

  let printer fields =
    let field (n, t) =
      let field = apply_nolbl (t.print |> Option.get) [exp_id n] in
      let field_name = string_ n in
      (string_concat ~sep:"=" [field_name; field], (lid_loc n, pat_s n))
    in
    try
      let fields = List.map field fields in
      let fields, pat = List.split fields in
      let app = string_concat ~sep:"; " fields in
      let app = string_concat [string_ "{"; app; string_ "}"] in
      lambda (Pat.record pat Closed) app |> Option.some
    with Invalid_argument _ -> None

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
          |> lambda (Pat.record pat Closed)
          |> Option.some
      | _ -> (*record with 0 field*) assert false
    with Invalid_argument _ -> None

  let collector fields =
    let field (n, t) =
      (apply_nolbl (t.spec |> Option.get) [exp_id n], (lid_loc n, pat_s n))
    in
    try
      let fields = List.map field fields in
      let fields, pat = List.split fields in
      match fields with
      | h :: tl ->
          List.fold_left ( &&@ ) h tl
          |> lambda (Pat.record pat Closed)
          |> Option.some
      | _ -> (*record with 0 field*) assert false
    with Invalid_argument _ -> None

  let make fields =
    let c = cardinality fields in
    let g = generator fields in
    let p = printer fields in
    let s = specification fields in
    let col = collector fields in
    make p g s c col
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
    if !Gegen.dom <> "rs" then
      match Gegen.solve_ct ct spec with
      | Some (gen, card) ->
          {typ with gen= Some gen; spec= Some spec; card= Finite card}
      | _ -> default
    else default

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
    | Some (gen, card) ->
        {typ with gen= Some gen; spec= Some spec; card= Finite card}
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

  let printer = Some (lambda_s "_" (string_ "(_ -> _)"))

  let make _input output =
    let c = Card.Unknown in
    let g = generator output.gen in
    let p = printer in
    let s = None in
    let col = None in
    make p g s c col
end
