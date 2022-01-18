type t' = Int of int | Add of t * t

and t = {annotation: string; data: t'}
