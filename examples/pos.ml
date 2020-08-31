type p_int = int [@satisfying (fun x -> x >= 0)]

let x : p_int = 2

let add (x:p_int) (y:p_int) : p_int = x + y
