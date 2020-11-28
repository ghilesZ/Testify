(* lift numeric operation to boolean ones *)
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

module Make (D : Numeric) = struct
  include D

  let filter space constr : (t * Lang.constr) Consistency.t =
    let open Lang in
    let open Consistency in
    let rec aux num = function
      | Boolop (c1, Or, c2) -> (
        match aux num c1 with
        | Sat -> Sat
        | Unsat -> aux num c2
        | Filtered ((n1, c1'), _) as x -> (
          match aux num c2 with
          | Sat -> Sat
          | Unsat -> x
          | Filtered ((n2, c2'), _) ->
              let union = join n1 n2 in
              Filtered ((union, Boolop (c1', Or, c2')), false) ) )
      | Boolop (c1, And, c2) -> (
        match aux num c1 with
        | Unsat -> Unsat
        | Sat -> aux num c2
        | Filtered ((n1, c1'), sat1) as x -> (
          match aux n1 c2 with
          | Sat -> x
          | Unsat -> Unsat
          | Filtered ((num', c2'), sat2) ->
              Filtered ((num', Boolop (c1', And, c2')), sat1 && sat2) ) )
      | Boolop (c1, Imply, c2) -> aux num (Boolop (negation c1, Or, c2))
      | Comparison (a1, cmp, a2) as x ->
          map (fun n -> (n, x)) (filter num a1 cmp a2)
      | Rejection _ -> assert false
    in
    aux space constr
end
