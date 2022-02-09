(* Generator generation for constrained types *)

open Migrate_parsetree
open Signatures
open Ast_410
open Parsetree
open Helper
module Conv = Convert (OCaml_410) (OCaml_current)
open Tools

let dom = ref "box"

let max_size = ref 16

let dom_name () =
  match !dom with "box" -> Format.asprintf "box_%i" !max_size | x -> x

let get_int s = apply_runtime "get_int" [string_ s]

let get_float s = apply_runtime "get_float" [string_ s]

(* fills the '_' of a pattern *)
let fill =
  let get_name = id_gen_gen () in
  let rec aux p =
    match p.ppat_desc with
    (* we prefix the name with % to avoid name clash *)
    | Ppat_any ->
        {p with ppat_desc= Ppat_var (def_loc ("%" ^ fst (get_name ())))}
    | Ppat_var _ -> p
    | Ppat_tuple ptup -> {p with ppat_desc= Ppat_tuple (List.map aux ptup)}
    | _ -> raise (Lang.OutOfSubset "pattern")
  in
  aux

(* compute the set of integer and the set of float values in a core_type *)
let collect_ct core_type pattern : SSet.t * SSet.t =
  let rec aux int_set float_set ct pat =
    match (ct.ptyp_desc, pat.ppat_desc) with
    | Ptyp_constr ({txt= Lident "int"; _}, []), Ppat_var {txt= ptxt; _} ->
        (SSet.add ptxt int_set, float_set)
    | Ptyp_constr ({txt= Lident "float"; _}, []), Ppat_var {txt= ptxt; _} ->
        (int_set, SSet.add ptxt float_set)
    | Ptyp_tuple ttup, Ppat_tuple ptup ->
        List.fold_left2
          (fun (i_s, f_s) tt pt -> aux i_s f_s tt pt)
          (int_set, float_set) ttup ptup
    | _ ->
        let msg =
          Format.asprintf "type %a and pattern %a are incompatible"
            print_coretype ct print_pat pattern
        in
        raise (Lang.OutOfSubset msg)
  in
  aux SSet.empty SSet.empty core_type (fill pattern)

(* compute the set of integer and the set of float values in a record *)
let collect_record labs : SSet.t * SSet.t =
  List.fold_left
    (fun (i_s, f_s) {pld_name; pld_type; _} ->
      let i, f = collect_ct pld_type (Pat.of_string pld_name.txt) in
      (SSet.union i i_s, SSet.union f f_s) )
    (SSet.empty, SSet.empty) labs

(* given a type 't' and a pattern, builds an exepression corresponding to a
   reconstruction function of type 'instance -> t' *)
let flatten_ct_ind core_type pattern =
  let rec aux ct pat =
    match (ct.ptyp_desc, pat.ppat_desc) with
    | Ptyp_constr ({txt= Lident "int"; _}, []), Ppat_var {txt= ptxt; _}
     |Ptyp_constr ({txt= Lident "float"; _}, []), Ppat_var {txt= ptxt; _} ->
        List.assoc ptxt
    | Ptyp_tuple t, Ppat_tuple p ->
        fun v -> List.map2 (fun t p -> aux t p v) t p |> tuple
    | _ -> raise (Lang.OutOfSubset "core_type or pattern")
  in
  aux core_type (fill pattern)

let flatten_record_ind labs =
  let r =
    List.fold_left
      (fun acc {pld_name; pld_type; _} ->
        let r = flatten_ct_ind pld_type (Pat.of_string pld_name.txt) in
        (fun vars -> (lid_loc pld_name.txt, r vars)) :: acc )
      [] labs
  in
  fun vars -> record (List.map (fun r -> r vars) r) None

(* given a type 't' and a pattern, builds an exepression corresponding to a
   reconstruction function of type 'instance -> t' *)
(* TODO: handle more patterns (e.g. _, as) *)
let flatten_ct core_type pattern =
  let rec aux ct pat =
    match (ct.ptyp_desc, pat.ppat_desc) with
    | Ptyp_constr ({txt= Lident "int"; _}, []), Ppat_var {txt= ptxt; _} ->
        get_int ptxt
    | Ptyp_constr ({txt= Lident "float"; _}, []), Ppat_var {txt= ptxt; _} ->
        get_float ptxt
    | Ptyp_tuple ttup, Ppat_tuple ptup ->
        let sons =
          List.fold_left2 (fun acc tt pt -> aux tt pt :: acc) [] ttup ptup
        in
        let b = List.rev_map (fun f -> apply_nolbl f [exp_id "i"]) sons in
        lambda_s "i" (tuple b)
    | _ -> raise (Lang.OutOfSubset "core_type or pattern")
  in
  aux core_type (fill pattern)

let flatten_record labs =
  let r =
    List.fold_left
      (fun acc {pld_name; pld_type; _} ->
        let r = flatten_ct pld_type (Pat.of_string pld_name.txt) in
        (lid_loc pld_name.txt, apply_nolbl r [exp_id "i"]) :: acc )
      [] labs
  in
  lambda_s "i" (record r None)

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
let craft_generator inner outer total pattern r_dep r_ind =
  let inner =
    List.map
      (fun (w, g) ->
        (Q.div (Q.of_bigint w) (Q.of_bigint total) |> Q.to_float, g) )
      inner
  in
  let outer =
    List.map
      (fun (w, g, r) ->
        (Q.div (Q.of_bigint w) (Q.of_bigint total) |> Q.to_float, g, r) )
      outer
  in
  let gen g =
    lambda_s "rs"
      ( match g with
      | Dependant g -> apply_nolbl r_dep [g]
      | Independant g -> r_ind g )
  in
  match (inner, outer) with
  | [(_, g)], [] ->
      gen g (* lighter generated code when the cover is a single element *)
  | _ ->
      let outer_gens =
        List.fold_left
          (fun acc (w, reject, g) ->
            let g = apply_runtime "reject" [lambda pattern reject; gen g] in
            cons_exp (tuple [float_ w; g]) acc )
          empty_list_exp (List.rev outer)
      in
      let inner_outer_gens =
        List.fold_left
          (fun acc (w, g) -> cons_exp (tuple [float_ w; gen g]) acc)
          outer_gens (List.rev inner)
      in
      apply_runtime "weighted" [inner_outer_gens]

let set_dom = function
  | ("box" | "poly" | "rs") as x -> dom := x
  | x -> Format.asprintf "Invalid domain %s" x |> invalid_arg

let set_size n = max_size := n

let get_generators i_s f_s constr =
  match !dom with
  | "box" -> Cover.Box.get_generators i_s f_s constr
  | "poly" -> Cover.Pol.get_generators i_s f_s constr
  | _ -> assert false

(* generator for constrained core types *)
let solve_ct ct sat =
  try
    let pat, body = split_fun sat in
    let constr = Lang.of_ocaml body in
    let i_s, f_s = collect_ct ct pat in
    let unflatten = flatten_ct ct pat in
    let unflatten_ind = flatten_ct_ind ct pat in
    let inner, outer, total = get_generators i_s f_s constr !max_size in
    let g = craft_generator inner outer total pat unflatten unflatten_ind in
    Some (g, total)
  with e ->
    Log.warn "solver failure %s on type %a" (Printexc.to_string e)
      print_coretype ct ;
    None

(* generator for constrained type declarations *)
let solve_td td sat =
  let flatten_record labs sat _td =
    let pat, body = split_fun sat in
    let constr = Lang.of_ocaml body in
    let i_s, f_s = collect_record labs in
    let unflatten = flatten_record labs in
    let unflatten_ind = flatten_record_ind labs in
    let inner, outer, total = get_generators i_s f_s constr !max_size in
    let g = craft_generator inner outer total pat unflatten unflatten_ind in
    Some (g, total)
  in
  let flatten_abstract td sat =
    Option.bind td.ptype_manifest (fun ct -> solve_ct ct sat)
  in
  try
    match td.ptype_kind with
    | Ptype_abstract -> flatten_abstract td sat
    | Ptype_record labs -> flatten_record labs sat td
    | Ptype_variant _ -> None
    | Ptype_open -> None
  with e ->
    Log.warn "solver failure %s on type@.%a" (Printexc.to_string e)
      print_type_decl td ;
    None
