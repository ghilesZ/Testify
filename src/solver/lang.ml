open Migrate_parsetree
open Ast_410
open Helper
open Parsetree
module Conv = Convert (OCaml_410) (OCaml_current)

type constr =
  | Rejection of expression
  | Boolop of constr * lop * constr
  | Comparison of comparison

and lop = Imply | And | Or

and comparison = arith * cmp * arith

and cmp = Lt | Leq | Gt | Geq | Eq | Diseq

and arith =
  | Int of int
  | Float of float
  | Binop of arith * bop * arith
  | Neg of arith
  | Var of string

and bop = Add | Sub | Mul | Div | Pow

(* exception we raise when we try to handle a term that does not belong to
   the language subset *)
exception OutOfSubset of string

let of_ocaml (expr : expression) : constr =
  let handle_cmp cmp =
    match cmp.pexp_desc with
    | Pexp_ident {txt= Lident i; _} -> (
      match i with
      | ">=" -> Geq
      | "<=" -> Leq
      | ">" -> Gt
      | "<" -> Lt
      | "=" -> Eq
      | "<>" -> Diseq
      | x -> raise (OutOfSubset ("operator " ^ x)) )
    | _ -> raise (OutOfSubset "comparison not an ident")
  in
  let handle_op op =
    match op.pexp_desc with
    | Pexp_ident {txt= Lident i; _} -> (
      match i with
      | "+" -> Add
      | "-" -> Sub
      | "*" -> Mul
      | "/" -> Div
      | "+." -> Add
      | "-." -> Sub
      | "*." -> Mul
      | "/." -> Div
      | "**" -> Pow
      | x -> raise (OutOfSubset ("operator " ^ x)) )
    | _ -> raise (OutOfSubset "operator not an ident")
  in
  let rec numeric e =
    match e.pexp_desc with
    | Pexp_apply (op, [(Nolabel, arg1); (Nolabel, arg2)]) ->
        Binop (numeric arg1, handle_op op, numeric arg2)
    | Pexp_apply
        ( {pexp_desc= Pexp_ident {txt= Lident ("-" | "-."); _}; _}
        , [(Nolabel, a)] ) ->
        Neg (numeric a)
    | Pexp_constant (Pconst_integer (s, None)) -> Int (int_of_string s)
    | Pexp_constant (Pconst_float (s, None)) -> Float (float_of_string s)
    | Pexp_ident {txt= Lident i; _} -> Var i
    | _ ->
        let msg =
          Format.asprintf "numeric value : %a" Pprintast.expression
            (Conv.copy_expression e)
        in
        raise (OutOfSubset msg)
  in
  let rec boolean e =
    let msg =
      Format.asprintf "boolean value : %a" Pprintast.expression
        (Conv.copy_expression e)
    in
    match e.pexp_desc with
    | Pexp_apply (({pexp_desc= Pexp_ident {txt= Lident i; _}; _} as op), args)
      -> (
      match (i, args) with
      | "ocaml", [(Nolabel, a)] -> Rejection a
      | _, [(Nolabel, a1); (Nolabel, a2)] -> (
        match i with
        | "&&" -> Boolop (boolean a1, And, boolean a2)
        | "||" -> Boolop (boolean a1, Or, boolean a2)
        | "=>" -> Boolop (boolean a1, Imply, boolean a2)
        | _ -> Comparison (numeric a1, handle_cmp op, numeric a2) )
      | _ -> raise (OutOfSubset msg) )
    | _ -> raise (OutOfSubset msg)
  in
  boolean expr

let to_ocaml (c:constr) : expression =
  let lop = function
    | And -> exp_id "&&"
    | Or -> exp_id "||"
    | Imply -> lambda_s "x" (lambda_s "y" (apply_nolbl_s "||" [apply_nolbl_s "not" [exp_id "x"]; exp_id "y"]))
  in
  let binop = function
    | Add -> "+"
    | Sub -> "-"
    | Mul -> "*"
    | Div -> "/"
    | Pow -> "**"
  in
  let rec arith = function
    | Int i -> int_exp i
    | Float f -> float_exp f
    | Var s -> exp_id s
    | Neg x -> (* FIXME: get the type of the underlying expression *)
       apply_nolbl_s "-" [arith x]
    | Binop (a1,b,a2) -> apply_nolbl_s (binop b) [arith a1; arith a2]
  in
  let cmp_to_string = function
    | Leq -> "<="
    | Lt -> "<"
    | Geq -> ">="
    | Gt -> ">"
    | Eq -> "="
    | Diseq -> "<>"
  in
  let rec aux = function
    | Rejection e -> e
    | Boolop (c1,op,c2) -> apply_nolbl (lop op) [aux c1; aux c2]
    | Comparison (a1,cmp,a2) ->  apply_nolbl_s (cmp_to_string cmp)
                                   [arith a1; arith a2]
  in aux c
