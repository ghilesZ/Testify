type desc = Int of int | Add of t * t

and t = {annotation: int; desc: desc}
