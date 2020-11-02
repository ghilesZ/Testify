open Migrate_parsetree
open Ast_410
open Parsetree
open Ast_helper
open Helper

open Apron
open Apronext

let manager = Box.manager_alloc()

(* exception we raise when we try to handle a term that does not
   belong to the subset of type langage we can handle *)
exception OutOfSubset

module SSet = Set.Make(String)

(* Parsetree.expression of type 'instance -> int' or 'instance -> float' *)
let constructors =
  Types.empty
  |> add_s "int" (fun v -> apply_nolbl_s "Testify_runtime.get_int" [string_exp v])
  |> add_s "float" (fun v -> apply_nolbl_s "Testify_runtime.get_float" [string_exp v])

(* given a type 't' and a pattern, builds an exepression corresponding
   to a reconstruction function of type 'instance -> t' *)
(* TODO: handle more patterns (e.g. _, as) *)
let reconstruct core_type pattern =
  let rec aux int_set float_set ct pat =
    match ct.ptyp_desc,pat.ppat_desc with
    | Ptyp_constr({txt=Lident "int";_},[]), Ppat_var {txt=ptxt;_} ->
       let r = apply_nolbl_s "Testify_runtime.get_int" [string_exp ptxt] in
       r,SSet.add ptxt int_set,float_set
    | Ptyp_constr({txt=Lident "float";_},[]), Ppat_var {txt=ptxt;_} ->
       let r = apply_nolbl_s "Testify_runtime.get_float" [string_exp ptxt] in
       r,int_set,SSet.add ptxt float_set
    | Ptyp_tuple ttup, Ppat_tuple ptup ->
       let sons,i_s,f_s = List.fold_left2 (fun (acc,i_s,f_s) tt pt ->
                              let s',i_s,f_s = aux i_s f_s tt pt in
                              (s'::acc),i_s,f_s
                            ) ([],int_set,float_set) ttup ptup in
       let b = List.map (fun f -> apply_nolbl f [exp_id "i"]) (List.rev sons) in
       lambda_s "i" (Exp.tuple b),i_s,f_s
    | _ -> raise OutOfSubset
  in
  aux SSet.empty SSet.empty core_type pattern

(* fills the '_' of a pattern *)
let rec fill p =
  match p.ppat_desc with
  (* we prefix the name with % to avoid ame clash *)
  | Ppat_any -> {p with ppat_desc = Ppat_var (none_loc ("%"^get_name ()))}
  | Ppat_var _ -> p
  | Ppat_tuple ptup -> {p with ppat_desc = Ppat_tuple (List.map fill ptup)}
  | _ -> raise OutOfSubset

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
        | _ -> raise OutOfSubset)
    | _ -> raise OutOfSubset
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
        | _ -> raise OutOfSubset)
    | _ -> raise OutOfSubset
  in
  let rec numeric e =
    match e.pexp_desc with
    | Pexp_apply(op, [Nolabel, arg1; Nolabel, arg2]) ->
       (handle_op op) (numeric arg1) (numeric arg2)
    | Pexp_constant(Pconst_integer (s,None)) ->
       Texprext.cst env (Coeff.s_of_int (int_of_string s))
    | Pexp_constant(Pconst_float (s,None)) ->
       Texprext.cst env (Coeff.s_of_float (float_of_string s))
    | _ -> raise OutOfSubset
  in
  let comparison e =
    match e.pexp_desc with
    | Pexp_apply(op, [Nolabel, arg1; Nolabel, arg2]) ->
       (handle_cmp op) (numeric arg1) (numeric arg2)
    | _ -> raise OutOfSubset
  in
  comparison expr

(* given a type declaration and a pattern, we build a generator *)
let abstract td pat body =
  let pat' = fill pat in
  let r,i_s,f_s = reconstruct td pat' in
  let i_s = SSet.elements i_s |> List.map Var.of_string |> Array.of_list in
  let f_s = SSet.elements f_s |> List.map Var.of_string |> Array.of_list in
  let env = Environment.make i_s f_s in
  let constr = predicate_to_constraint env body in
  let abs =  Abstract1.top manager env in
  let abs' = Abstractext.filter_tcons manager abs constr in
  let boxgen = Boxgen.compile_box abs' in
  lambda_s "rs" (apply_nolbl r [apply_nolbl boxgen [exp_id "rs"]])
