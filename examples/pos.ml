(* type p_int = int [@satisfying (fun x -> x >= 0)]
 *
 * let x : p_int = 2
 *
 * let abs (x:int) : p_int = if x < 0 then -x else x *)

type itv = int * int [@satisfying (fun (x,y) -> x <= y)]

let[@gen itv] gen_itv (rs:Random.State.t) =
  Random.set_state rs;
  let x = Random.int max_int in
  let y = Random.int max_int in
  min x y, max x y
