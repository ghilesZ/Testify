type itv = Z.t * Z.t [@satisfying (fun (x,y) -> x <= y)]

open Z

let neg ((low,high):itv) : itv = -high,-low

(* let[@gen itv] spawn rs =
 *   let pair_gen = QCheck.Gen.pair QCheck.Gen.int QCheck.Gen.int in
 *   let i,j = pair_gen rs in
 *   let zi= Z.of_int i and zj = Z.of_int j in
 *   (min zi zj),(max zi zj) *)

let add ((low1,high1):itv) ((low2,high2):itv) : itv =
  (low1 + low2), (high1 + high2)
