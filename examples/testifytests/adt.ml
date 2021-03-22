type pos = (int[@satisfying fun x -> x >= 0])

type optpos = None | Some of pos

let output (x : pos) : optpos = if x < 0 then None else Some x

let input (x : optpos) : pos = match x with None -> 0 | Some x -> x
