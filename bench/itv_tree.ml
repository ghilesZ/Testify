type interval_tree_x =
  | LeafX
  | NodeX of
      (int[@collect 1])
      * interval_tree_y
      * interval_tree_y
      * (int[@collect 2])
          [@@satisfying fun x -> increasing x 1 && increasing x 2]
and interval_tree_y =
  | LeafY
  | NodeY of
      ( (int[@collect 3])
         * interval_tree_x
         * interval_tree_x
         * (int[@collect 4]) )
        [@@satisfying fun x -> increasing x 3 && increasing x 4]

let id (t:interval_tree_x) : interval_tree_x = t
