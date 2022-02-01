type map =
  | Node of map * (int[@collect]) * int * map
  (* left * key * value * right *)
  | Leaf
[@@satisfying increasing]
