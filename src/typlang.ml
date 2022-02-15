open Migrate_parsetree.Ast_410
open Parsetree
open Helper
open Asttypes

type t =
  | Ident of string
  | Var of string
  | Sum of constructor list
  | Tuple of t list
  | Arrow of t list
  | Record of (string * t) list
  | Apply of t list * string
  | Constrained of t * Lang.constr

and constructor = string * t list

let rec print fmt (typ : t) =
  match typ with
  | Ident s -> Format.fprintf fmt "%s" s
  | Var s -> Format.fprintf fmt "'%s" s
  | Sum l ->
      (Format.pp_print_list
         ~pp_sep:(fun fmt () -> Format.fprintf fmt "@,| ")
         print_constructor )
        fmt l
  | Tuple l -> (Format.pp_print_list ~pp_sep:(sep " * ") print) fmt l
  | Arrow l -> (Format.pp_print_list ~pp_sep:(sep " -> ") print) fmt l
  | Record fields ->
      let print_pair fmt (name, typ) =
        Format.fprintf fmt "%s : %a" name print typ
      in
      Format.fprintf fmt "{%a}"
        (Format.pp_print_list
           ~pp_sep:(fun fmt () -> Format.fprintf fmt " -> ")
           print_pair )
        fields
  | Apply (args, name) ->
      Format.fprintf fmt "%a %s"
        (Format.pp_print_list ~pp_sep:(sep ", ") print)
        args name
  | Constrained (t, constr) ->
      Format.fprintf fmt "%a s.t %a" print t Lang.print constr

and print_constructor fmt (name, arg) =
  Format.fprintf fmt "%s of %a" name
    (Format.pp_print_list ~pp_sep:(sep " * ") print)
    arg

let rec printer get = function
  | Var _ -> lambda_s "_" (string_ "()")
  | Ident s -> get s
  | Sum l -> List.map (printer_constructor get) l |> function_
  | Tuple l ->
      let get_name = id_gen_gen () in
      let np p =
        let n, id = get_name () in
        (apply_nolbl (printer get p) [id], Pat.of_string n)
      in
      let names, pats = List.split (List.map np l) in
      let b = string_concat ~sep:", " names in
      let b' = string_concat [string_ "("; b; string_ ")"] in
      lambda (Pat.tuple pats) b'
  | Arrow _ as funtyp ->
      lambda_s "_" (string_ (Format.asprintf "%a" print funtyp))
  | Record fields -> (
      let field (n, t) =
        let field = apply_nolbl (printer get t) [exp_id n] in
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
          lambda (Pat.record_closed (List.rev pat)) app )
  | Apply (args, name) ->
      apply_nolbl (get name) (List.map (printer get) args)
  | Constrained (t, _constr) -> printer get t

and printer_constructor get (name, args) =
  let pat_exp p id =
    List.map
      (fun _ ->
        let p, e = id () in
        (Pat.of_string p, e) )
      p
    |> List.split
  in
  let id = id_gen_gen () in
  let constr pat = Pat.construct_s name pat in
  match args with
  | [] -> case (constr None) (string_ name)
  | [one] ->
      let pat, expr = id () in
      case
        (constr (Some (Pat.of_string pat)))
        (string_concat
           [ string_ (name ^ "(")
           ; apply_nolbl (printer get one) [expr]
           ; string_ ")" ] )
  | p ->
      let pat, exp = pat_exp p id in
      case
        (constr (Some (Pat.tuple pat)))
        (string_concat
           [string_ name; apply_nolbl (printer get (Tuple p)) [tuple exp]] )

let rec parse_ct ct : t =
  match get_attribute_pstr "satisfying" ct.ptyp_attributes with
  | Some e ->
      Constrained (parse_ct {ct with ptyp_attributes= []}, Lang.of_ocaml e)
  | None -> (
    match ct.ptyp_desc with
    | Ptyp_var var -> Var var
    | Ptyp_constr ({txt; _}, []) -> Ident (lid_to_string txt)
    | Ptyp_constr ({txt; _}, l) ->
        Apply (List.map parse_ct l, lid_to_string txt)
    | Ptyp_poly (_, _ct) -> failwith "explicit polymorphic type"
    | Ptyp_tuple tup -> Tuple (List.map parse_ct tup)
    | Ptyp_arrow (Nolabel, input, output) ->
        Arrow [parse_ct input; parse_ct output]
    | _ -> failwith (Format.asprintf "%a" print_coretype ct) )
