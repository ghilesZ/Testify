type binary_tree =
  | Node of binary_tree * (int[@collect]) * binary_tree
  | Leaf
[@@satisfying fun x -> increasing x]
