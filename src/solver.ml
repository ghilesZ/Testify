open Migrate_parsetree
open Ast_410
open Apron
open Apronext
open Parsetree
module Conv = Convert (OCaml_410) (OCaml_current)

type constr =
  | RejectionSampling of expression
  | Boolop of constr * lop * constr
  | Comparison of arith * cmp * arith

and lop = Imply | And | Or

and cmp = Lt | Leq | Gt | Geq | Eq | Diseq

and arith =
  | Int of int
  | Float of float
  | Binop of arith * bop * arith
  | Neg of arith
  | Var of string

and bop = Add | Sub | Mul | Div | Pow

(* exception we raise when we try to handle a term that does not belong to
   the subset of type langage we can handle *)
exception OutOfSubset of string

let predicate_to_constraint (expr : expression) : constr =
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
  let comparison e =
    match e.pexp_desc with
    | Pexp_apply (op, [(Nolabel, arg1); (Nolabel, arg2)]) ->
        Comparison (numeric arg1, handle_cmp op, numeric arg2)
    | _ ->
        let msg =
          Format.asprintf "boolean value : %a" Pprintast.expression
            (Conv.copy_expression e)
        in
        raise (OutOfSubset msg)
  in
  let rec boolean e =
    match e.pexp_desc with
    | Pexp_apply
        ({pexp_desc= Pexp_ident {txt= Lident "ocaml"; _}; _}, [(Nolabel, a)])
      ->
        RejectionSampling a
    | Pexp_apply
        ( {pexp_desc= Pexp_ident {txt= Lident i; _}; _}
        , [(Nolabel, a1); (Nolabel, a2)] ) -> (
      match i with
      | "&&" -> Boolop (boolean a1, And, boolean a2)
      | "||" -> Boolop (boolean a1, Or, boolean a2)
      | "=>" -> Boolop (boolean a1, Imply, boolean a2)
      | _ -> comparison e )
    | _ ->
        let msg =
          Format.asprintf "boolean value : %a" Pprintast.expression
            (Conv.copy_expression e)
        in
        raise (OutOfSubset msg)
  in
  boolean expr
