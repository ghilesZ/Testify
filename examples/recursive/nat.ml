(** Tests the support for infinite types that are not recursive. *)

(* This is recursive *)
type nat = Zero | Succ of nat

let rec le n m =
  match (n, m) with
  | Zero, _ -> true
  | _, Zero -> false
  | Succ n, Succ m -> le n m

(* This is not *)
type interval = nat * nat [@@satisfying fun (x, y) -> le x y]

let incr ((n, m) : interval) : interval = (Succ n, Succ m)

let incr_buggy ((n, m) : interval) : interval = (Succ n, m)
