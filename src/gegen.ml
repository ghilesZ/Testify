(* Generator generation for constrained types *)

open Migrate_parsetree
open Ast_410
open Parsetree
open Ast_helper
open Helper
module Conv = Convert (OCaml_410) (OCaml_current)
open Tools

let bench = ref ""

let dom = ref "box"

let max_size = ref 8

let dom_name () =
  match !dom with "box" -> Format.asprintf "box_%i" !max_size | x -> x

let get_int s = apply_nolbl_s "get_int" [string_ s]

let get_float s = apply_nolbl_s "get_float" [string_ s]

(* fills the '_' of a pattern *)
let fill =
  let get_name = id_gen_gen () in
  let rec aux p =
    match p.ppat_desc with
    (* we prefix the name with % to avoid name clash *)
    | Ppat_any ->
        {p with ppat_desc= Ppat_var (none_loc ("%" ^ fst (get_name ())))}
    | Ppat_var _ -> p
    | Ppat_tuple ptup -> {p with ppat_desc= Ppat_tuple (List.map aux ptup)}
    | _ -> raise (Lang.OutOfSubset "pattern")
  in
  aux

(* given a type 't' and a pattern, builds an exepression corresponding to a
   reconstruction function of type 'instance -> t' *)
(* TODO: handle more patterns (e.g. _, as) *)
let flatten_ct core_type pattern =
  let rec aux int_set float_set ct pat =
    match (ct.ptyp_desc, pat.ppat_desc) with
    | Ptyp_constr ({txt= Lident "int"; _}, []), Ppat_var {txt= ptxt; _} ->
        (get_int ptxt, SSet.add ptxt int_set, float_set)
    | Ptyp_constr ({txt= Lident "float"; _}, []), Ppat_var {txt= ptxt; _} ->
        (get_float ptxt, int_set, SSet.add ptxt float_set)
    | Ptyp_tuple ttup, Ppat_tuple ptup ->
        let sons, i_s, f_s =
          List.fold_left2
            (fun (acc, i_s, f_s) tt pt ->
              let s', i_s, f_s = aux i_s f_s tt pt in
              (s' :: acc, i_s, f_s))
            ([], int_set, float_set) ttup ptup
        in
        let b =
          List.map (fun f -> apply_nolbl f [exp_id "i"]) (List.rev sons)
        in
        (lambda_s "i" (Exp.tuple b), i_s, f_s)
    | _ -> raise (Lang.OutOfSubset "core_type or pattern")
  in
  aux SSet.empty SSet.empty core_type (fill pattern)

let flatten_record labs _pattern =
  match labs with
  | [] -> assert false (*empty record*)
  | _ ->
      let r, i_s, f_s =
        List.fold_left
          (fun (acc, i_s, f_s) {pld_name; pld_type; _} ->
            let r, i, f = flatten_ct pld_type (Pat.var pld_name) in
            ( (lid_loc pld_name.txt, apply_nolbl r [exp_id "i"]) :: acc
            , SSet.union i i_s
            , SSet.union f f_s ))
          ([], SSet.empty, SSet.empty)
          labs
      in
      (lambda_s "i" (Exp.record r None), i_s, f_s)

let split_fun f =
  match f.pexp_desc with
  | Pexp_fun (Nolabel, None, pat, body) -> (pat, body)
  | _ ->
      Format.asprintf "was expecting a function but got %a"
        Pprintast.expression (Conv.copy_expression f)
      |> failwith

(* over-approximation of the actual cardinality as outer elements are likely
   to have less inhabittants *)
let cardinality inner outer =
  Z.add
    (List.to_seq inner |> Seq.map fst |> Seq.fold_left Z.add Z.zero)
    (List.to_seq outer |> Seq.map fst |> Seq.fold_left Z.add Z.zero)

(* builds a generator list, sorted by probability of being chosen (from most
   likely to less likely) *)
let craft_generator inner outer total pattern r =
  let inner =
    List.map
      (fun (w, g) ->
        (Q.div (Q.of_bigint w) (Q.of_bigint total) |> Q.to_float, g))
      inner
  in
  let outer =
    List.map
      (fun (w, g, r) ->
        (Q.div (Q.of_bigint w) (Q.of_bigint total) |> Q.to_float, g, r))
      outer
  in
  match (inner, outer) with
  | [(_, g)], [] ->
      r |><| g
      (* lighter generated code when the cover is a single element *)
  | _ ->
      let outer_gens =
        List.fold_left
          (fun acc (w, reject, g) ->
            let g =
              apply_nolbl_s "reject" [lambda pattern reject; r |><| g]
            in
            cons_exp (Exp.tuple [float_dec w; g]) acc)
          empty_list_exp (List.rev outer)
      in
      let inner_outer_gens =
        List.fold_left
          (fun acc (w, g) ->
            cons_exp (Exp.tuple [float_dec w; r |><| g]) acc)
          outer_gens (List.rev inner)
      in
      apply_nolbl_s "weighted" [inner_outer_gens]

let set_dom = function
  | ("box" | "poly" | "rs") as x -> dom := x
  | x -> Format.asprintf "Invalid domain %s" x |> invalid_arg

let set_size n = max_size := n

let get_generators i_s f_s constr =
  match !dom with
  | "box" -> Cover.Box.get_generators i_s f_s constr
  | "poly" -> Cover.Pol.get_generators i_s f_s constr
  | _ -> assert false

let print_loc fmt (l : Location.t) =
  let fn = Filename.(l.loc_start.pos_fname |> basename |> chop_extension) in
  Format.fprintf fmt "%s%i" fn l.loc_start.pos_lnum

let showbench gen td umetric constr i f =
  if !bench <> "" then (
    let td, loc =
      match td with
      | None -> ("", "")
      | Some td ->
          ( Format.asprintf "%a" print_td {td with ptype_manifest= None}
          , Format.asprintf "%a" print_loc td.ptype_loc )
    in
    let name = "gen/" ^ !bench ^ loc ^ ".ml" in
    let nb_vars = SSet.cardinal i + SSet.cardinal f in
    let stat = Format.asprintf "%s %i" (Lang.get_kind constr) nb_vars in
    if Sys.file_exists name then
      Format.eprintf "warning overwritting file %s\n%!" name ;
    let out = open_out name in
    let fmt = Format.formatter_of_out_channel out in
    Format.fprintf fmt "%s\n" td ;
    Format.fprintf fmt "open Testify_runtime\nlet gen=@.@[%a@]\n%s %f%!"
      print_expression gen
      ( {|let () = Format.printf "|} ^ loc ^ " " ^ stat ^ " " ^ !bench
      ^ {| %i %.2F\n%!" ((speed_estimate 1000000 gen)/1000) |} )
      umetric ;
    Format.pp_print_flush fmt () ;
    flush out ;
    close_out out )

let u_metric inner total =
  let add = List.fold_left (fun acc (w, _e) -> Z.add acc w) Z.zero in
  let ratio = Q.make (add inner) total in
  Q.to_float ratio

(* generator for constrained core types *)
let solve_ct ct sat =
  let res =
    try
      let pat, body = split_fun sat in
      let unflatten, i_s, f_s = flatten_ct ct pat in
      let constr = Lang.of_ocaml body in
      let inner, outer, total = get_generators i_s f_s constr !max_size in
      let g = craft_generator inner outer total pat unflatten in
      (* showbench g None (u_metric inner total) ; *)
      Some (g, total)
    with Lang.OutOfSubset _ -> None
  in
  res

let flatten_record labs sat td =
  try
    let pat, body = split_fun sat in
    let constr = Lang.of_ocaml body in
    let unflatten, i_s, f_s = flatten_record labs pat in
    let inner, outer, total = get_generators i_s f_s constr !max_size in
    let g = craft_generator inner outer total pat unflatten in
    showbench g (Some td) (u_metric inner total) constr i_s f_s ;
    Some (g, total)
  with Lang.OutOfSubset _ -> None

let flatten_abstract td sat =
  Option.bind td.ptype_manifest (fun ct ->
      let res =
        try
          let pat, body = split_fun sat in
          let unflatten, i_s, f_s = flatten_ct ct pat in
          let constr = Lang.of_ocaml body in
          let inner, outer, total =
            get_generators i_s f_s constr !max_size
          in
          let g = craft_generator inner outer total pat unflatten in
          showbench g (Some td) (u_metric inner total) constr i_s f_s ;
          Some (g, total)
        with Lang.OutOfSubset _ -> None
      in
      res)

(* generator for constrained type declarations *)
let solve_td td sat =
  let res =
    try
      match td.ptype_kind with
      | Ptype_abstract -> flatten_abstract td sat
      | Ptype_record labs -> flatten_record labs sat td
      | Ptype_variant _ -> None
      | Ptype_open -> None
    with Lang.OutOfSubset _ -> None
  in
  res
