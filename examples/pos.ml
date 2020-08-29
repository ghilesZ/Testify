type p_int = int[@satisfying (fun x -> x >= 0)]

let x : p_int = 2

let abs (x:int) : p_int =
  if x < 0 then -x else x

let _ = QCheck.(Test.make ~count:1000
   int (fun x -> (fun x -> x >= 0) (abs x)))
