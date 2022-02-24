type increasing_list =
  | Nil
  | Cons of (int[@collect]) * increasing_list
[@@satisfying increasing]
let id (l:increasing_list) : increasing_list = l

(* type strictly_increasing_list = *)
(*   | Nil *)
(*   | Cons of (int[@collect]) * strictly_increasing_list *)
(* [@@satisfying increasing_strict] *)
(* let id (l:strictly_increasing_list) : strictly_increasing_list = l *)

(* type assoc_list = *)
(*   | Nil *)
(*   | Cons of (int[@collect]) * int * assoc_list *)
(* [@@satisfying alldiff] *)
(* let id (l:assoc_list) : assoc_list = l *)

(* type bstree = *)
(*   | Node of bstree * (int[@collect]) * bstree *)
(*   | Leaf *)
(* [@@satisfying increasing] *)
(* let id_bst (t:bstree) : bstree = t  *)

