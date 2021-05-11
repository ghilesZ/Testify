type itv = (int * int[@satisfying fun (x, y) -> x <= y])

(* buggy due to -min_int. unlikely to be detected by testify *)
let neg ((low, high) : itv) : itv = (-high, -low)

(* buggy due to integer overflow. should be detected by testify *)
let add ((low1, high1) : itv) ((low2, high2) : itv) : itv =
  (low1 + low2, high1 + high2)
