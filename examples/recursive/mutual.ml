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
      (int[@collect 3])
      * interval_tree_x
      * interval_tree_x
      * (int[@collect 4])
[@@satisfying fun x -> increasing x 3 && increasing x 4]

let id (x : interval_tree_x) : interval_tree_x = x

let bad_quad (x : interval_tree_x) : interval_tree_x =
  match x with LeafX -> LeafX | NodeX (l, t1, t2, u) -> NodeX (u, t1, t2, l)

let (q : interval_tree_x) =
  NodeX
    ( -2042366550
    , NodeY
        ( -1673580173
        , NodeX (-387811496, LeafY, LeafY, -141482023)
        , LeafX
        , 719338301 )
    , NodeY (797799694, LeafX, LeafX, 1784138236)
    , 1993851112 )
