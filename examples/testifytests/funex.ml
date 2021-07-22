type nat = (int[@satisfying fun x -> x >= 0])

let apply (f : nat -> nat) (n : nat) : nat = f n
