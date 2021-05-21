type nat = (int[@satisfying fun x -> x >= 0])

(* let square (x : int) : p_int =
 *   let two32 = 0x1_0000_0000 in
 *   if -two32 < x && x < two32 then x * x
 *   else invalid_arg "square only works for values smaller than 2^32"
 *
 * let abs (x : int) : p_int = if x >= 0 then x else -x *)

let mul (x : nat) (y : nat) : nat = x * y
