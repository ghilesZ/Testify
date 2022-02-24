type assoc_list =
  | Nil
  | Cons of (int[@collect]) * int * assoc_list
[@@satisfying alldiff]
let id (l:assoc_list) : assoc_list = l
