open Migrate_parsetree
open Ast_410
open Parsetree
open Helper
open Ast_helper
open Location

(** representation of an OCaml type *)

type t =
  { gen: expression option
  ; spec: expression option
  ; card: Z.t option
  ; print: expression option }

let print_expr fmt e =
  Format.fprintf fmt "```ocaml@.@[%a@]\n```" print_expression e

let print_card =
  let z15 = Z.of_int 32768 in
  let close_log z =
    let down = Z.log2 z in
    let up = Z.log2 z in
    let two = Z.of_int 2 in
    if Z.sub z (Z.shift_left two down) < Z.sub (Z.shift_left two up) z then
      down
    else up
  in
  fun fmt z ->
    (* if cardinality is big, we print it as a power of two for easier
       reading *)
    if Z.gt z z15 then Format.fprintf fmt "~2<sup>%i</sup>" (close_log z)
    else Format.fprintf fmt "%a" Z.pp_print z

let print fmt {gen; spec; card; print} =
  Format.fprintf fmt "- Printer: " ;
  ( match print with
  | None -> Format.fprintf fmt "no printer derived"
  | Some e -> Format.fprintf fmt "\n%a" print_expr e ) ;
  Format.fprintf fmt "\n" ;
  Format.fprintf fmt "- Specification: " ;
  ( match spec with
  | None -> Format.fprintf fmt " no specification derived"
  | Some e -> Format.fprintf fmt "\n%a" print_expr e ) ;
  Format.fprintf fmt "\n" ;
  Format.fprintf fmt "- Cardinality estimation: " ;
  ( match card with
  | None -> Format.fprintf fmt " no cardinality derived"
  | Some c -> Format.fprintf fmt "%a" print_card c ) ;
  Format.fprintf fmt "\n" ;
  Format.fprintf fmt "- Generator: " ;
  match gen with
  | None -> Format.fprintf fmt " no generator derived"
  | Some e -> Format.fprintf fmt "\n%a" print_expr e

let get_generator p = p.gen

let get_specification p = p.spec

let get_cardinality p = p.card

let get_printer p = p.print

let empty = {gen= None; spec= None; card= None; print= None}

let add_printer info p = {info with print= Some p}

let add_generator info g = {info with gen= Some g}

let add_specification info s = {info with spec= Some s}

let free g c p = {print= Some p; gen= Some g; spec= None; card= Some c}

let make print gen spec card = {gen; spec; card; print}

(* Predefined types *)

let unit = free (exp_id "QCheck.Gen.unit") Z.one (exp_id "QCheck.Print.unit")

let bool =
  free (exp_id "QCheck.Gen.bool") (Z.of_int 2) (exp_id "string_of_bool")

let char =
  free (exp_id "QCheck.Gen.char") (Z.of_int 256) (exp_id "string_of_char")

let int =
  free (exp_id "QCheck.Gen.int")
    (Z.pow (Z.of_int 2) (Sys.int_size - 1))
    (exp_id "string_of_int")

let float =
  free
    (exp_id "QCheck.Gen.float")
    (Z.pow (Z.of_int 2) 64)
    (exp_id "string_of_float")

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
           (Typ.constr (lid_loc "error") [alpha; beta]))
      "error" vars kind
  in
  {vars; body}

(** {1 Type composition} *)

(** tuples *)
module Product = struct
  let gen_body typs =
    List.map
      (function
        | {gen= Some g; _} -> apply_nolbl g [exp_id "rs"] | _ -> raise Exit)
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

  let cardinality typs =
    try
      List.fold_left
        (fun acc -> function {card= Some c; _} -> Z.mul acc c
          | _ -> raise Exit)
        Z.one typs
      |> Option.some
    with Exit -> None

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

  let make typs =
    make (printer typs) (generator typs) (specification typs)
      (cardinality typs)
end

(** ADTs *)
module Sum = struct
  let cardinality variants =
    try
      List.fold_left
        (fun acc (_constr, args) ->
          match Product.cardinality args with
          | Some c -> Z.add acc c
          | _ -> raise Exit)
        Z.zero variants
      |> Option.some
    with Exit -> None

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

  let generator variants totalcard =
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
                 let card = Product.cardinality typs |> Option.get in
                 Helper.pair (weight card)
                   (constr_generator constr typs |> Option.get))
               variants) ]
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
          (string_concat
             [string_ (txt ^ "("); apply_nolbl p [expr]; string_ ")"])
        |> Option.some
    | [{print= None; _}] -> None
    | p ->
        let pat, exp =
          List.map
            (fun _ ->
              let p, e = id () in
              (pat_s p, e))
            p
          |> List.split
        in
        Option.map
          (fun print ->
            Exp.case
              (constr (Some (Pat.tuple pat)))
              (apply_nolbl print [Exp.tuple exp]))
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
    | [{spec; _}] ->
        let prop = Option.get spec in
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
              (pat_s p, e))
            p
          |> List.split
        in
        let pat = Pat.tuple pat in
        ( pat
        , Option.map
            (fun spec ->
              Exp.case (constr (Some pat)) (apply_nolbl spec [Exp.tuple exp]))
            (Product.specification args) )

  let specification variants =
    try
      let cases = List.map (fun (c, a) -> constr_spec c a) variants in
      if List.for_all (fun (_, c) -> c = None) cases then None
      else
        Some
          (Exp.function_
             (List.map
                (function p, None -> Exp.case p true_ | _, Some c -> c)
                cases))
    with Exit | Invalid_argument _ -> None

  let make variants =
    let c = cardinality variants in
    let g = generator variants c in
    let p = printer variants in
    let s = specification variants in
    make p g s c
end

module Record = struct
  let cardinality _fields = None

  let generator fields =
    let field name t =
      (lid_loc name, apply_nolbl (t.gen |> Option.get) [exp_id "rs"])
    in
    let fields = List.map (fun (n, t) -> field n t) fields in
    Exp.record fields None |> lambda_s "rs" |> Option.some

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

  let make fields =
    let c = cardinality fields in
    let g = generator fields in
    let p = printer fields in
    let s = specification fields in
    make p g s c
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
                    |> invalid_arg)
                r1 r2)
             c)
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
      ; card= None }
    in
    if !Gegen.dom <> "rs" then
      match Gegen.solve_ct ct spec with
      | Some (gen, card) ->
          {typ with gen= Some gen; spec= Some spec; card= Some card}
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
      ; card= None }
    in
    if !Gegen.dom <> "rs" then
      match Gegen.solve_td td e with
      | Some (gen, card) ->
          {typ with gen= Some gen; spec= Some spec; card= Some card}
      | _ -> default
    else
      try
        Gegen.showbench
          (default.gen |> Option.get)
          (Some td) 1. (Lang.Rejection e) Tools.SSet.empty Tools.SSet.empty ;
        default
      with _ -> () ; default
end
