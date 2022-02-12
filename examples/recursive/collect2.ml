type t = Empty | Cons of (int[@collect 1]) * (int[@collect 2]) * t
[@@satisfying fun x -> increasing x 1 && increasing x 2]

let some_list : t = Cons (0, 0, Cons (1, 3, Cons (4, 5, Empty)))

let some_list_buggy : t = Cons (4, 0, Cons (1, 3, Cons (4, 5, Empty)))

let cons_buggy (l : t) ((a, b) : int * int) : t = Cons (a, b, l)
