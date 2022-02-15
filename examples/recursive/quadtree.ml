type interval_tree_x =
  | LeafX
  | NodeX of
      ( (int[@collect 1])
      * interval_tree_y
      * interval_tree_y
      * (int[@collect 2]) )
[@@satisfying fun x -> increasing x 1 && increasing x 2]

and interval_tree_y =
  | LeafY
  | NodeY of
      ( (int[@collect 3])
      * interval_tree_x
      * interval_tree_x
      * (int[@collect 4]) )
[@@satisfying fun x -> increasing x 3 && increasing x 4]

let quad : interval_tree_x =
  NodeX (0, NodeY (1, LeafX, LeafX, 50), NodeY (3, LeafX, LeafX, 60), 100)

type itv_tree =
  | Leaf
  | Node of ((int[@collect 1]) * itv_tree * itv_tree * (int[@collect 2]))
[@@satisfying fun x -> increasing x 1 && increasing x 2]
