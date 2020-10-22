type itv = int * int [@@satisfying (fun (x,y) -> x <= y)]

let neg ((low,high):itv) : itv = -high,-low

let add ((low1,high1):itv) ((low2,high2):itv) : itv =
  (low1 + low2), (high1 + high2)
