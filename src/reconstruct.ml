open Migrate_parsetree
open Ast_410
open Parsetree
open Ast_helper

open Helper

module Conv = Convert (OCaml_410) (OCaml_current)

open Apron
open Apronext

let manager = Polka.manager_alloc_strict ()

(* exception we raise when we try to handle a term that does not
   belong to the subset of type langage we can handle *)
exception OutOfSubset of string

module SSet = Set.Make(String)

(* Parsetree.expression of type 'instance -> int' or 'instance -> float' *)
let constructors =
  Types.empty
  |> add_s "int" (fun v -> apply_runtime "get_int" [string_exp v])
  |> add_s "float" (fun v -> apply_runtime "get_float" [string_exp v])

(* given a type 't' and a pattern, builds an exepression corresponding
   to a reconstruction function of type 'instance -> t' *)
(* TODO: handle more patterns (e.g. _, as) *)
let reconstruct core_type pattern =
  let rec aux int_set float_set ct pat =
    match ct.ptyp_desc,pat.ppat_desc with
    | Ptyp_constr({txt=Lident "int";_},[]), Ppat_var {txt=ptxt;_} ->
       let r = apply_runtime "get_int" [string_exp ptxt] in
       r,SSet.add ptxt int_set,float_set
    | Ptyp_constr({txt=Lident "float";_},[]), Ppat_var {txt=ptxt;_} ->
       let r = apply_runtime "get_float" [string_exp ptxt] in
       r,int_set,SSet.add ptxt float_set
    | Ptyp_tuple ttup, Ppat_tuple ptup ->
       let sons,i_s,f_s = List.fold_left2 (fun (acc,i_s,f_s) tt pt ->
                              let s',i_s,f_s = aux i_s f_s tt pt in
                              (s'::acc),i_s,f_s
                            ) ([],int_set,float_set) ttup ptup in
       let b = List.map (fun f -> apply_nolbl f [exp_id "i"]) (List.rev sons) in
       lambda_s "i" (Exp.tuple b),i_s,f_s
    | _ -> raise (OutOfSubset "core_type or pattern")
  in
  aux SSet.empty SSet.empty core_type pattern

(* fills the '_' of a pattern *)
let rec fill p =
  match p.ppat_desc with
  (* we prefix the name with % to avoid ame clash *)
  | Ppat_any -> {p with ppat_desc = Ppat_var (none_loc ("%"^get_name ()))}
  | Ppat_var _ -> p
  | Ppat_tuple ptup -> {p with ppat_desc = Ppat_tuple (List.map fill ptup)}
  | _ -> raise (OutOfSubset "pattern")

let predicate_to_constraint env expr =
 let handle_cmp cmp =
    match cmp.pexp_desc with
    | Pexp_ident {txt=Lident i;_} ->
       (match i with
        | ">=" -> Tconsext.geq
        | "<=" -> Tconsext.leq
        | ">"  -> Tconsext.gt
        | "<"  -> Tconsext.lt
        | "="  -> Tconsext.eq
        | "<>" -> Tconsext.diseq
        | x -> raise (OutOfSubset ("operator "^x)))
    | _ -> raise (OutOfSubset "comparison not an ident")
  in
  let handle_op op =
    match op.pexp_desc with
    | Pexp_ident {txt=Lident i;_} ->
       (match i with
        | "+"  -> Texprext.add ~typ:Int
        | "-"  -> Texprext.sub ~typ:Int
        | "*"  -> Texprext.mul ~typ:Int
        | "/"  -> Texprext.div ~typ:Int
        | "+." -> Texprext.add ~typ:Real
        | "-." -> Texprext.sub ~typ:Real
        | "*." -> Texprext.mul ~typ:Real
        | "/." -> Texprext.div ~typ:Real
        | "**" -> Texprext.pow ~typ:Real
        | x -> raise (OutOfSubset ("operator "^x)))
    | _ -> raise (OutOfSubset "operator not an ident")
  in
  let rec numeric e =
    match e.pexp_desc with
    | Pexp_apply(op, [Nolabel, arg1; Nolabel, arg2]) ->
       (handle_op op) (numeric arg1) (numeric arg2)
    | Pexp_constant(Pconst_integer (s,None)) ->
       Texprext.cst env (Coeff.s_of_int (int_of_string s))
    | Pexp_constant(Pconst_float (s,None)) ->
       Texprext.cst env (Coeff.s_of_float (float_of_string s))
    | Pexp_ident {txt=Lident i;_} -> Texprext.var env (Var.of_string i)
    | _ ->
       let msg = Format.asprintf "numeric value : %a"
                   Pprintast.expression (Conv.copy_expression e) in
       raise (OutOfSubset msg)
  in
  let comparison e =
    match e.pexp_desc with
    | Pexp_apply(op, [Nolabel, arg1; Nolabel, arg2]) ->
       (handle_cmp op) (numeric arg1) (numeric arg2)
    | _ ->
       let msg = Format.asprintf "boolean value : %a"
                   Pprintast.expression (Conv.copy_expression e) in
       raise (OutOfSubset msg)
  in
  comparison expr

let split_fun f =
  match f.pexp_desc with
  | Pexp_fun(Nolabel,None,pat,body) -> pat,body
  | _ -> Format.asprintf "was expecting a function but got %a"
           Pprintast.expression (Conv.copy_expression f)
         |> failwith

(* given a type declaration and a pattern, we build a generator *)
let abstract_core_type td sat =
  let pat,body=split_fun sat in
  let pat' = fill pat in
  let r,i_s,f_s = reconstruct td pat' in
  let i_s = SSet.elements i_s |> List.map Var.of_string |> Array.of_list in
  let f_s = SSet.elements f_s |> List.map Var.of_string |> Array.of_list in
  let env = Environment.make i_s f_s in
  let constr = predicate_to_constraint env body in
  let abs = Boxgen.ocaml_box env in
  let abs' = Abstractext.filter_tcons manager abs constr in
  let boxgen = Boxgen.compile_box abs' in
  lambda_s "rs" (apply_nolbl r [apply_nolbl boxgen [exp_id "rs"]])

let abstract t sat =
  try
    match t.ptype_kind with
    |	Ptype_abstract ->
       (match t.ptype_manifest with
        | Some ct -> Some (abstract_core_type ct sat)
        | None -> None)
    |	Ptype_variant _ -> None
    |	Ptype_record _labs -> (* todo records *) None
    |	Ptype_open -> None
  with OutOfSubset msg -> Format.printf "%s\n%!" msg; None
