type p_int = int[@satisfying (fun x -> x >= 0)]

let x : p_int = 2

let abs (x:int) : p_int =
  if x < 0 then -x else x
