type map =
  | Node of map * (int[@collect]) * int * map
  (* left * key * value * right *)
  | Leaf
[@@satisfying increasing]

let good : map = Node (Leaf, 2, 2, Node (Leaf, 3, 4, Leaf))

let bad : map = Node (Leaf, 6, 2, Node (Leaf, 3, 4, Leaf))

let rec insert (key : int) (value : int) (bt : map) : map =
  match bt with
  | Leaf -> Node (Leaf, key, value, Leaf)
  | Node (l, key', value', r) ->
      if key < key' then Node (insert key value l, key', value', r)
      else Node (l, key', value', insert key value r)

let rec insert_buggy (key : int) (value : int) (bt : map) : map =
  match bt with
  | Leaf -> Node (Leaf, key, value, Leaf)
  | Node (l, key', value', r) ->
      if key < key' then Node (insert_buggy key' value l, key, value', l)
      else Node (l, key', value', insert_buggy key value r)
