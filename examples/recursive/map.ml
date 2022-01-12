type map =
  | Node of map * (int[@collect]) * int * map
  (* left * key * value * right *)
  | Leaf
[@@satisfying
  fun x ->
    let l = depth_first_search x in
    increasing l && all_diff l]
