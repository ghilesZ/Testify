type 'a pair = 'a * 'a

type pos = (int[@satisfying fun x -> x >= 0])

let doublepos (a : pos) : pos pair = (a, a)
