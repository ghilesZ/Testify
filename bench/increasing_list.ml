type increasing_list =
  | Nil
  | Cons of (int[@collect]) * increasing_list
[@@satisfying increasing]
let id (l:increasing_list) : increasing_list = l
