open Tools

module type Numeric = sig
  type t

  val init : SSet.t -> SSet.t -> t

  val filter : t -> Lang.arith -> Lang.cmp -> Lang.arith -> t Consistency.t

  val join : t -> t -> t

  val compile : t -> Migrate_parsetree.Ast_410.Parsetree.expression

  val split : t -> t list

  val volume : t -> float

  val print : Format.formatter -> t -> unit

  val to_drawable : t -> Picasso.Drawable.t
end

module type Abs = sig
  include Numeric

  val filter : t -> Lang.constr -> (t * Lang.constr) Consistency.t
end
