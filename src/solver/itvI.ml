(* integer intervals *)
type t = Z.t * Z.t

let print fmt (l, u) = Format.fprintf fmt "[%a;%a]" Z.pp_print l Z.pp_print u

let z2 = Z.of_int 2

let join (l1, h1) (l2, h2) = (Z.min l1 l2, Z.max h1 h2)

let meet (l1, h1) (l2, h2) : t option =
  let low = Z.max l1 l2 in
  let high = Z.min h1 h2 in
  if Z.gt low high then None else Some (low, high)

let range (a, b) = Z.sub b a

let split (l, h) =
  if l = h then invalid_arg "split"
  else
    let mid = Z.add l (Z.div (Z.sub h l) z2) in
    [(l, mid); (Z.add mid Z.one, h)]

(* Forward operators *)

let add (l1, h1) (l2, h2) = (Z.add l1 l2, Z.add h1 h2)

let sub (l1, h1) (l2, h2) = (Z.sub l1 h2, Z.sub h1 l2)

let neg (l1, h1) = (Z.neg h1, Z.neg l1)

let mul (_l1, _h1) (_l2, _h2) = failwith "itvI.mul"

let div (_l1, _h1) (_l2, _h2) = failwith "itvI.div"

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
  if Z.leq h1 l2 then Sat
  else if Z.gt l1 h2 then Unsat
  else Filtered (((l1, Z.min h1 h2), (Z.max l1 l2, h2)), l1 = h1 || l2 = h2)

let filter_lt ((l1, h1) : t) ((l2, h2) : t) : (t * t) Consistency.t =
  let open Consistency in
  if Z.lt h1 l2 then Sat
  else if Z.geq l1 h2 then Unsat
  else
    Filtered
      ( ((l1, Z.min h1 (Z.sub h2 Z.one)), (Z.max (Z.add l1 Z.one) l2, h2))
      , l1 = h1 || l2 = h2 )

let filter_eq ((l1, h1) : t) ((l2, h2) : t) : t Consistency.t =
  let open Consistency in
  if l1 = h1 && l2 = h2 && l1 = l2 then Sat
  else
    let l = max l1 l2 and h = min h1 h2 in
    if l <= h then Filtered ((l, h), false) else Unsat

let filter_diseq ((l1, h1) as i1 : t) ((l2, h2) as i2 : t) :
    (t * t) Consistency.t =
  let open Consistency in
  if l1 = h1 && l2 = h2 && l1 = l2 then Unsat
  else if Option.is_some (meet i1 i2) then
    Filtered ((i1, i2), l1 = h1 || l2 = h2)
  else Sat

(* compilation *)
let compile ((inf, sup) : t) =
  let open Helper in
  let i = inf |> Z.to_int |> int_ in
  let s = sup |> Z.to_int |> int_ in
  apply_nolbl_s "mk_int_range" [i; s]
