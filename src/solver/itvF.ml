(* float interval with rational bounds *)

type t = Q.t * Q.t

let print fmt (l, u) = Format.fprintf fmt "[%a;%a]" Q.pp_print l Q.pp_print u

let q2 = Q.of_int 2

let join (l1, h1) (l2, h2) = (Q.min l1 l2, Q.max h1 h2)

let meet (l1, h1) (l2, h2) =
  let low = Q.max l1 l2 in
  let high = Q.min h1 h2 in
  if Q.gt low high then None else Some (low, high)

let split (l, h) =
  if l = h then invalid_arg "split"
  else
    let mid = Q.add l (Q.div (Q.sub h l) q2) in
    [(l, mid); (mid, h)]

let range (l, h) = Q.sub h l |> Q.to_float

(* Forward operators *)

let add (l1, h1) (l2, h2) = (Q.add l1 l2, Q.add h1 h2)

let sub (l1, h1) (l2, h2) = (Q.sub l1 h2, Q.sub h1 l2)

let neg (l1, h1) = (Q.neg h1, Q.neg l1)

(* Backward operators *)

let merge_bot2 x y =
  match (x, y) with
  | None, _ | _, None -> None
  | Some a, Some b -> Some (a, b)

let bwd_add i1 i2 r : (t * t) option =
  merge_bot2 (meet i1 (sub r i2)) (meet i2 (sub r i1))

let bwd_sub (i1 : t) (i2 : t) (r : t) : (t * t) option =
  merge_bot2 (meet i1 (add i2 r)) (meet i2 (sub i1 r))

let bwd_neg (i : t) (r : t) : t option = meet i (neg r)

(* Guards *)

let filter_leq ((l1, h1) : t) ((l2, h2) : t) : (t * t) Consistency.t =
  let open Consistency in
  if Q.leq h1 l2 then Sat
  else if Q.gt l1 h2 then Unsat
  else Filtered (((l1, Q.min h1 h2), (Q.max l1 l2, h2)), false)

let filter_lt ((l1, h1) as i1 : t) ((l2, h2) as i2 : t) :
    (t * t) Consistency.t =
  let open Consistency in
  if Q.lt h1 l2 then Sat
  else if l1 = h1 && i1 = i2 then Unsat
  else Filtered (((l1, Q.min h1 h2), (Q.max l1 l2, h2)), false)

let filter_eq ((l1, h1) as i1 : t) ((l2, h2) as i2 : t) : t Consistency.t =
  let open Consistency in
  if l1 = h1 && i1 = i2 then Sat
  else
    let l = Q.max l1 l2 and u = Q.min h1 h2 in
    if Q.leq l u then Filtered ((l, u), false) else Unsat

let filter_diseq ((l1, h1) as i1 : t) ((l2, h2) as i2 : t) :
    (t * t) Consistency.t =
  let open Consistency in
  if Q.equal l1 h1 && Q.equal l2 h2 && Q.equal l1 l2 then Unsat
  else
    let l = Q.max l1 l2 and u = Q.min h1 h2 in
    if Q.leq l u then Filtered ((i1, i2), false) else Sat

(* compilation *)
let compile ((inf, sup) : t) =
  let open Helper in
  let i = inf |> Q.to_float |> float_exp in
  let s = sup |> Q.to_float |> float_exp in
  [exp_id "rs"]
  |> apply_nolbl (apply_runtime "float_range" [i; s])
  |> apply_runtime_1 "mk_float"
  |> lambda_s "rs"
