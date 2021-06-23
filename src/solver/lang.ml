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
  | NegF of arith
  | ToInt of arith
  | ToFloat of arith
  | Var of string

and bop = Add | Sub | Mul | Div | Pow | AddF | SubF | MulF | DivF

let neg_cmp = function
  | Lt -> Geq
  | Leq -> Gt
  | Gt -> Leq
  | Geq -> Lt
  | Eq -> Diseq
  | Diseq -> Eq

let rec negation = function
  | Comparison (a, cmp, b) -> Comparison (a, neg_cmp cmp, b)
  | Boolop (a, Or, b) -> Boolop (negation a, And, negation b)
  | Boolop (a, And, b) -> Boolop (negation a, Or, negation b)
  | Boolop (a, Imply, b) -> Boolop (a, And, negation b)
  | Rejection _ -> assert false

let is_rejection = function Rejection _ -> true | _ -> false

(* exception we raise when we try to handle a term that does not belong to
   the language subset *)
exception OutOfSubset of string

let of_ocaml (expr : expression) : constr =
  let handle_cmp cmp =
    match cmp.pexp_desc with
    | Pexp_ident {txt= Lident i; _} -> (
      match i with
      | ">=" | ">=." -> Geq
      | "<=" | "<=." -> Leq
      | ">" | ">." -> Gt
      | "<" | "<." -> Lt
      | "=" | "=." -> Eq
      | "<>" | "<>." -> Diseq
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
      | "+." -> AddF
      | "-." -> SubF
      | "*." -> MulF
      | "/." -> DivF
      | "**" -> Pow
      | x -> raise (OutOfSubset ("operator " ^ x)) )
    | _ -> raise (OutOfSubset "operator not an ident")
  in
  let rec numeric e =
    match e.pexp_desc with
    | Pexp_apply
        ( {pexp_desc= Pexp_ident {txt= Lident "float_of_int"; _}; _}
        , [(Nolabel, arg)] ) ->
        ToFloat (numeric arg)
    | Pexp_apply
        ( {pexp_desc= Pexp_ident {txt= Lident "int_of_float"; _}; _}
        , [(Nolabel, arg)] ) ->
        ToFloat (numeric arg)
    | Pexp_apply (op, [(Nolabel, arg1); (Nolabel, arg2)]) ->
        Binop (numeric arg1, handle_op op, numeric arg2)
    | Pexp_apply
        ({pexp_desc= Pexp_ident {txt= Lident "-"; _}; _}, [(Nolabel, a)]) ->
        Neg (numeric a)
    | Pexp_apply
        ({pexp_desc= Pexp_ident {txt= Lident "-."; _}; _}, [(Nolabel, a)]) ->
        NegF (numeric a)
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

type typ = I | F

let to_string = function I -> "int" | F -> "float"

let coerce_to t1 t2 =
  if t1 <> t2 then
    invalid_arg
      (Format.asprintf
         "This expression has type %s but an expressaion was expected of \
          type %s"
         (to_string t1) (to_string t2))

let get_typ ints reals =
  let rec loop = function
    | Int _ -> I
    | Float _ -> F
    | Var s ->
        if Tools.SSet.mem s ints then I
        else if Tools.SSet.mem s reals then F
        else invalid_arg (Format.asprintf "unboud value %s" s)
    | Neg x ->
        coerce_to (loop x) I ;
        I
    | NegF x ->
        coerce_to (loop x) F ;
        F
    | Binop (a1, b, a2) ->
        let optyp = match b with Add | Sub | Mul | Div -> I | _ -> F in
        coerce_to (loop a1) optyp ;
        coerce_to (loop a2) optyp ;
        optyp
    | ToInt x ->
        coerce_to (loop x) F ;
        I
    | ToFloat x ->
        coerce_to (loop x) I ;
        F
  in
  loop

let to_ocaml ints reals (c : constr) : expression =
  let lop = function
    | And -> exp_id "( && )"
    | Or -> exp_id "( || )"
    | Imply ->
        lambda_s "x"
          (lambda_s "y"
             (apply_nolbl_s "( || )"
                [apply_nolbl_s "not" [exp_id "x"]; exp_id "y"]))
  in
  let binop = function
    | Add -> "Int.add"
    | Sub -> "Int.sub"
    | Mul -> "Int.mul"
    | Div -> "Int.div"
    | Pow -> "Float.pow"
    | AddF -> "Float.add"
    | SubF -> "Float.sub"
    | MulF -> "Float.mul"
    | DivF -> "Float.div"
  in
  let rec arith = function
    | Int i -> int_ i
    | Float f -> float_ f
    | Var s -> exp_id s
    | Neg x -> apply_nolbl_s "( ~- )" [arith x]
    | NegF x -> apply_nolbl_s "( ~-. )" [arith x]
    | Binop (a1, b, a2) -> apply_nolbl_s (binop b) [arith a1; arith a2]
    | ToInt x -> apply_nolbl_s "int_of_float" [arith x]
    | ToFloat x -> apply_nolbl_s "float" [arith x]
  in
  let cmp_to_string typ cmp =
    match typ with
    | F -> (
      match cmp with
      | Leq -> "(<=.)"
      | Lt -> "(<.)"
      | Geq -> "(>=.)"
      | Gt -> "(>.)"
      | Eq -> "(=.)"
      | Diseq -> "(<>.)" )
    | I -> (
      match cmp with
      | Leq -> "(<=)"
      | Lt -> "(<)"
      | Geq -> "(>=)"
      | Gt -> "(>)"
      | Eq -> "(=)"
      | Diseq -> "(<>)" )
  in
  let rec aux = function
    | Rejection e -> e
    | Boolop (c1, op, c2) -> apply_nolbl (lop op) [aux c1; aux c2]
    | Comparison (a1, cmp, a2) ->
        let t1 = get_typ ints reals a1 in
        let t2 = get_typ ints reals a2 in
        coerce_to t1 t2 ;
        apply_nolbl_s (cmp_to_string t1 cmp) [arith a1; arith a2]
  in
  aux c

let unify c1 c2 =
  match (c1, c2) with
  | "other", _ | _, "other" -> "other"
  | "lin", _ | _, "lin" -> "lin"
  | "bc", "bc" -> "bc"
  | _ -> assert false

let get_kind c =
  let rec loop = function
    | Rejection _ -> "rs"
    | Boolop (c1, _lop, c2) ->
        Format.asprintf "%s" (unify (loop c1) (loop c2))
    | Comparison (Var _, (Geq | Leq | Lt | Gt), (Int _ | Float _)) -> "bc"
    | Comparison ((Int _ | Float _), (Geq | Leq | Lt | Gt), Var _) -> "bc"
    | Comparison (Var _, (Geq | Leq | Lt | Gt), Var _) -> "lin"
    | Comparison _ -> "other"
  in
  loop c

exception Split of constr * constr
