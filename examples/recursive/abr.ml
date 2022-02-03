type binary_tree =
  | Node of binary_tree * (int[@collect]) * binary_tree
  | Leaf
[@@satisfying increasing]

let rec insert (x : int) (bt : binary_tree) : binary_tree =
  match bt with
  | Leaf -> Node (Leaf, x, Leaf)
  | Node (l, x', r) ->
      if x < x' then Node (insert x l, x', r) else Node (l, x', insert x r)

let rec insert_buggy (x : int) (bt : binary_tree) : binary_tree =
  match bt with
  | Leaf -> Node (Leaf, x, Leaf)
  | Node (l, x', r) ->
      if x < x' then Node (insert_buggy x' l, x, r)
      else Node (l, x', insert_buggy x r)
