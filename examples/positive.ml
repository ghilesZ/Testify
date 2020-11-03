type p_int = int [@@satisfying (fun x -> x >= 0)]

let square (x:int) : p_int = x * x

let add (x:p_int) (y:p_int) : p_int = x + y
