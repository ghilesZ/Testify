type uniquelist = Empty | Cons of (int[@collect]) * uniquelist
[@@satisfying fun x -> alldiff x]

let rec add (x : int) (l : uniquelist) : uniquelist =
  match l with
  | Empty -> Cons (x, Empty)
  | Cons (h, tl) -> if x = h then l else Cons (h, add x tl)
