type t = Empty | Cons of (int[@collect 1]) * (int[@collect 2]) * t
[@@satisfying fun x -> increasing x 1 && increasing x 2]

let l1 : t = Cons (0, 0, Cons (1, 3, Cons (4, 5, Empty)))
