open Migrate_parsetree
open Ast_410
open Tools

module type Numeric = sig
  type t

  val filter : t -> Lang.arith -> Lang.cmp -> Lang.arith -> t Consistency.t

  val join : t -> t -> t

  val init : SSet.t -> SSet.t -> t

  val compile : t -> Migrate_parsetree.Ast_410.Parsetree.expression

  val split : t -> t list

  val volume : t -> float
end

module type Abs = sig
  type t

  val init : SSet.t -> SSet.t -> t

  val compile : t -> Parsetree.expression

  val split : t -> t list

  val filter : t -> Lang.constr -> (t * Lang.constr) Consistency.t

  val volume : t -> float
end
