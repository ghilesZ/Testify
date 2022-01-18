(* type binary_tree = Node of int * binary_tree * binary_tree | Leaf *)

(* let is_valid binary_tree =
 *   let rec loop pred = function
 *     | Leaf -> true
 *     | Node (x, left, right) ->
 *         pred x && loop (( > ) x) left && loop (( <= ) x) right
 *   in
 *   loop (fun _ -> true) *)

(* let rec is_sorted = function
 *   | x :: (y :: l as tl) -> x <= y && is_sorted tl
 *   | _ -> true
 *
 * let is_valid binary_tree =
 *   let rec collect acc = function
 *     | Leaf -> acc
 *     | Node (x, left, right) -> collect (x :: collect acc left) right
 *   in
 *   is_sorted (collect [] binary_tree) *)

type binary_tree =
  | Node of binary_tree * (int[@collect]) * binary_tree
  | Leaf
[@@satisfying fun x -> increasing x]
