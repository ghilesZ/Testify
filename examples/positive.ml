type p_int = int [@satisfying (fun x -> x >= 0)]

let square (x:int) : p_int = x * x
