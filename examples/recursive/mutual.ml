type pos = (int[@satisfying fun x -> 0 <= x])

type desc = Int of pos | Add of t * t

and t = {annotation: int; desc: desc}

let rec eval (x : t) : pos =
  match x.desc with Int n -> n | Add (x, y) -> eval x + eval y
