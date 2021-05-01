type nat = (int[@satisfying fun x -> x >= 0])

type sum = A of bool | B of bool * bool

let input (s : sum) : nat = match s with A _ -> 0 | B _ -> 1

let abs (nat : nat) : nat = abs nat
