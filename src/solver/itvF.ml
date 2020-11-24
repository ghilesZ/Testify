type t = Q.t * Q.t

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
