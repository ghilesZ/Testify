(* float interval with rational bounds *)

type t = Q.t * Q.t

let print fmt (l, u) = Format.fprintf fmt "[%a;%a]" Q.pp_print l Q.pp_print u

let q2 = Q.of_int 2

let join (l1, h1) (l2, h2) = (Q.min l1 l2, Q.max h1 h2)

let meet (l1, h1) (l2, h2) =
  let low = Q.max l1 l2 in
  let high = Q.min h1 h2 in
  if Q.gt low high then None else Some (low, high)

let subseteq (l1, h1) (l2, h2) = Q.leq l2 l1 && Q.leq h1 h2

let split (l, h) =
  if l = h then invalid_arg "split"
  else
    let mid = Q.add l (Q.div (Q.sub h l) q2) in
    [(l, mid); (mid, h)]

(* both non-zero *)
let how_many low high =
  if low < 0. && 0. < high then
    (*not same sign *)
    Int64.(
      add
        (sub (bits_of_float high) (bits_of_float min_float))
        (sub (bits_of_float (abs_float low)) (bits_of_float min_float)))
  else if (*same sign*) high < 0. then
    (*both negative*)
    Int64.(
      sub (bits_of_float (abs_float low)) (bits_of_float (abs_float high)))
  else
    (* both positive *)
    Int64.(sub (bits_of_float high) (bits_of_float low))

let how_many low high =
  if low = high then 1L
  else if low = 0. then how_many min_float high |> Int64.succ
  else if high = 0. then how_many low (-.min_float) |> Int64.succ
  else how_many low high

let range (l, h) = how_many (Q.to_float l) (Q.to_float h) |> Z.of_int64

(* Forward operators *)

let add (l1, h1) (l2, h2) = (Q.add l1 l2, Q.add h1 h2)

let sub (l1, h1) (l2, h2) = (Q.sub l1 h2, Q.sub h1 l2)

let neg (l1, h1) = (Q.neg h1, Q.neg l1)

let mul (l1, h1) (l2, h2) =
  let ac, ad = (Q.mul l1 l2, Q.mul l1 h2)
  and bc, bd = (Q.mul h1 l2, Q.mul h1 h2) in
  (Q.min (Q.min ac ad) (Q.min bc bd), Q.max (Q.max ac ad) (Q.max bc bd))

let div x y : t =
  let div_pos a b c d =
    (Q.min (Q.div a c) (Q.div a d), Q.max (Q.div b c) (Q.div b d))
  and div_neg a b c d =
    (Q.min (Q.div b c) (Q.div b d), Q.max (Q.div a c) (Q.div a d))
  in
  match (x, y) with
  | (a, b), (c, d) -> (
    match (Q.sign c, Q.sign d) with
    | 0, 0 -> failwith "division by zero"
    | 1, _ ->
        let r, s = div_pos a b c d in
        (r, s)
    | _, -1 ->
        let r, s = div_neg a b c d in
        (r, s)
    | _ ->
        let r1, s1 = div_pos a b (Q.max Q.one c) d
        and r2, s2 = div_neg a b c (Q.min Q.minus_one d) in
        (Q.min r1 r2, Q.max s1 s2) )

let rec pow (l, h) i =
  if i = 0 then (Q.one, Q.one)
  else if i = 1 then (l, h)
  else if i > 0 then pow (Q.mul l l, Q.mul h h) (i - 1)
  else pow (h, l) (-i)

let pow itv i =
  let i = Z.to_int i in
  pow itv i

(* Backward operators *)

let merge_bot2 x y =
  match (x, y) with
  | None, _ | _, None -> None
  | Some a, Some b -> Some (a, b)

let bwd_add i1 i2 r : (t * t) option =
  merge_bot2 (meet i1 (sub r i2)) (meet i2 (sub r i1))

let bwd_sub (i1 : t) (i2 : t) (r : t) : (t * t) option =
  merge_bot2 (meet i1 (add i2 r)) (meet i2 (sub i1 r))

let bwd_mul x y r : (t * t) option =
  (* r=x*y => (x=r/y or y=r=0) and (y=r/x or x=r=0)  *)
  let contains_zero o = subseteq (Q.zero, Q.zero) o in
  match
    ( ( if contains_zero y && contains_zero r then Some x
      else meet x (div r y) )
    , if contains_zero x && contains_zero r then Some y else meet y (div r x)
    )
  with
  | Some x, Some y -> Some (x, y)
  | _ -> None

let bwd_div i1 i2 _r : (t * t) option = Some (i1, i2)

let bwd_neg (i : t) (r : t) : t option = meet i (neg r)

let bwd_pow itv _i _r = Some itv

(* Guards *)

let filter_leq ((l1, h1) : t) ((l2, h2) : t) : (t * t) Consistency.t =
  let open Consistency in
  if Q.leq h1 l2 then Sat
  else if Q.gt l1 h2 then Unsat
  else Filtered (((l1, Q.min h1 h2), (Q.max l1 l2, h2)), l1 = h1 || l2 = h2)

let filter_lt ((l1, h1) as i1 : t) ((l2, h2) as i2 : t) :
    (t * t) Consistency.t =
  let open Consistency in
  if Q.lt h1 l2 then Sat
  else if (l1 = h1 && i1 = i2) || Q.gt l1 h2 then Unsat
  else Filtered (((l1, Q.min h1 h2), (Q.max l1 l2, h2)), l1 = h1 || l2 = h2)

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
  let i = inf |> Q.to_float |> float_ in
  let s = sup |> Q.to_float |> float_ in
  apply_nolbl_s "float_range" [i; s]
