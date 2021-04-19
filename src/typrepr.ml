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

let get_generator p = p.gen

let get_specification p = p.spec

let get_cardinality p = p.card

let get_printer p = p.print

let empty = {gen= None; spec= None; card= None; print= None}

let add_printer info p = {info with print= Some p}

let add_generator info g = {info with gen= Some g}

let add_specification info s = {info with spec= Some s}

let free g c p = {print= Some p; gen= Some g; spec= None; card= Some c}

let constrained g s c p =
  {print= Some p; gen= Some g; spec= Some s; card= Some c}

let make print gen spec card = {gen; spec; card; print}

(* Predefined types *)

let unit = free (exp_id "QCheck.Gen.unit") Z.one (exp_id "QCheck.Print.unit")

let bool =
  free (exp_id "QCheck.Gen.bool") (Z.of_int 2) (exp_id "string_of_bool")

let char =
  free (exp_id "QCheck.Gen.char") (Z.of_int 256) (exp_id "string_of_char")

let int =
  free (exp_id "QCheck.Gen.int")
    (Z.pow (Z.of_int 2) Sys.int_size)
    (exp_id "string_of_int")

let float =
  free
    (exp_id "QCheck.Gen.float")
    (Z.pow (Z.of_int 2) Sys.int_size)
    (exp_id "string_of_float")

(** {1 Type composition} *)

(** tuples *)
module Product = struct
  let generator typs =
    try
      List.map
        (function
          | {gen= Some g; _} -> apply_nolbl g [exp_id "x"] | _ -> raise Exit)
        typs
      |> Exp.tuple |> lambda_s "x" |> Option.some
    with Exit -> None

  let specification typs =
    let get_name = id_gen_gen () in
    let compose (pats, prop) p =
      match (prop, p.spec) with
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
    | l ->
        Option.map
          (fun g ->
            lambda_s "rs" (constr (Some (apply_nolbl g [exp_id "rs"]))))
          (Product.generator l)

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
    with Invalid_argument _ -> None

  let constr_spec {txt; _} args =
    let constr pat = Pat.construct (lid_loc txt) pat in
    match args with
    | [] -> Exp.case (constr None) true_ |> Option.some
    | [{spec; _}] ->
        let prop = Option.get spec in
        let id = id_gen_gen () in
        let p, e = id () in
        Exp.case (constr (Some (pat_s p))) (apply_nolbl prop [e])
        |> Option.some
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
        Option.map
          (fun spec ->
            Exp.case
              (constr (Some (Pat.tuple pat)))
              (apply_nolbl spec [Exp.tuple exp]))
          (Product.specification args)

  let specification variants =
    let cases = List.map (fun (c, a) -> constr_spec c a) variants in
    if List.for_all (( = ) None) cases then None
    else
      Some
        (Exp.function_
           (List.map
              (function None -> Exp.case (Pat.any ()) true_ | Some c -> c)
              cases))

  let make variants =
    let c = cardinality variants in
    let g = generator variants c in
    let p = printer variants in
    let s = specification variants in
    make p g s c
end
