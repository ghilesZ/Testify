type itv = int * int [@satisfying (fun (x,y) -> x <= y)]

let neg ((low,high):itv) : itv = -high,-low

let[@gen itv] spawn rs =
  let pair_gen = QCheck.Gen.pair QCheck.Gen.int QCheck.Gen.int in
  let i,j = pair_gen rs in
  (min i j),(max i j)

let add ((low1,high1):itv) ((low2,high2):itv) : itv =
  (low1 + low2), (high1 + high2)
