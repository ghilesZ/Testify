type 'a maybe = None | Some of 'a

type pos = int [@@satisfying fun x -> x >= 0]

let input (x : pos maybe) : pos = match x with None -> 0 | Some x -> x

let output (x : pos) : pos maybe = if x < 0 then None else Some x
