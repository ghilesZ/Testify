type nat = (int[@satisfying fun x -> x >= 0])

let abs (x : Int.t) : nat = if x >= 0 then x else -x
