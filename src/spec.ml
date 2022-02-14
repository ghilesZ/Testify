open Migrate_parsetree
open Ast_410
open Parsetree

type constr =
  | Constr of expression
  | GlobalConstraint of string
  | Bool of constr * bop * constr

and bop = And | Or
