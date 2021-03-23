type nat = (int[@satisfying fun x -> x > 0])

let rec log2 (x : nat) : (nat[@satisfying fun x -> x < 62]) =
  match x with 1 -> 0 | n -> 1 + log2 (n / 2)
