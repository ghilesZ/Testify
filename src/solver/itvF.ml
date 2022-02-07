(* float interval with rational bounds *)

type t = Range of Q.t * Q.t | Top

let print_range fmt (l, u) =
  Format.fprintf fmt "[%a;%a]" Q.pp_print l Q.pp_print u

let print fmt = function
  | Range (l, u) -> Format.fprintf fmt "%a" print_range (l, u)
  | Top -> Format.fprintf fmt "T"

let q2 = Q.of_int 2

let join i1 i2 =
  match (i1, i2) with
  | Range (l1, h1), Range (l2, h2) -> Range (Q.min l1 l2, Q.max h1 h2)
  | _ -> Top

let meet i1 i2 =
  match (i1, i2) with
  | Top, x | x, Top -> Some x
  | Range (l1, h1), Range (l2, h2) ->
      let low = Q.max l1 l2 in
      let high = Q.min h1 h2 in
      if Q.gt low high then None else Some (Range (low, high))

let subseteq_range (l1, h1) (l2, h2) = Q.leq l2 l1 && Q.leq h1 h2

let subseteq i1 i2 =
  match (i1, i2) with
  | _, Top -> true
  | Top, Range _ -> false
  | Range (l1, h1), Range (l2, h2) -> subseteq_range (l1, h1) (l2, h2)

let split_range ((l, h) as i) =
  if l = h then
    let msg = Format.asprintf "invalid split on range %a" print_range i in
    invalid_arg msg
  else
    let mid = Q.add l (Q.div (Q.sub h l) q2) in
    [(l, mid); (mid, h)]

let split = function
  | Top ->
      [ Range (Q.of_float neg_infinity, Q.zero)
      ; Range (Q.zero, Q.of_float infinity) ]
  | Range (l, h) as i ->
      if l = h then
        let msg = Format.asprintf "invalid split on range %a" print i in
        invalid_arg msg
      else
        let mid = Q.add l (Q.div (Q.sub h l) q2) in
        [Range (l, mid); Range (mid, h)]

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

let range = function
  | Top -> Z.of_int max_int
  | Range (l, h) -> Q.sub h l |> Q.to_bigint

(* Forward operators *)

let add (l1, h1) (l2, h2) = (Q.add l1 l2, Q.add h1 h2)

let sub (l1, h1) (l2, h2) = (Q.sub l1 h2, Q.sub h1 l2)

let neg (l1, h1) = (Q.neg h1, Q.neg l1)

let mul (l1, h1) (l2, h2) =
  let ac, ad = (Q.mul l1 l2, Q.mul l1 h2)
  and bc, bd = (Q.mul h1 l2, Q.mul h1 h2) in
  (Q.min (Q.min ac ad) (Q.min bc bd), Q.max (Q.max ac ad) (Q.max bc bd))

let div x y =
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

let pow_up x n = Q.of_float (Q.to_float x ** float n)

let pow_down = pow_up

let pow itv i =
  (* powers *)
  let pow (il, ih) (p : int) =
    match p with
    | 0 -> (Q.one, Q.one)
    | 1 -> (il, ih)
    | x ->
        if x > 1 then
          if x mod 2 = 1 then (pow_down il p, pow_up ih p)
          else if Q.leq il Q.zero && Q.geq ih Q.zero then
            (Q.zero, max (pow_up il p) (pow_up ih p))
          else if Q.geq il Q.zero then (pow_down il p, pow_up ih p)
          else (pow_down ih p, pow_up il p)
        else failwith "cant handle negatives powers"
  in
  let i = Z.to_int i in
  let res = pow itv i in
  (* Format.eprintf "%a ** %i = %a\n" print_range itv i print_range res ; *)
  res

let root_up x n = Q.of_float (exp (log (Q.to_float x) /. float (Z.to_int n)))

let root_down x n =
  Q.of_float (exp (log (Q.to_float x) /. float (Z.to_int n)))

(* nth-root *)
let root (il, ih) p =
  if p = Z.one then Some (il, ih)
  else if Z.gt p Z.one then
    if Z.rem p (Z.of_int 2) = Z.one then Some (root_down il p, root_up ih p)
    else if Q.lt ih Q.zero then None
    else if Q.leq il Q.zero then Some (Q.neg (root_down ih p), root_up ih p)
    else
      Some
        ( Q.min (Q.neg (root_down il p)) (Q.neg (root_down ih p))
        , Q.max (root_up il p) (root_up ih p) )
  else failwith "can only handle stricly positive roots"

let add i1 i2 =
  match (i1, i2) with
  | Range (l1, h1), Range (l2, h2) ->
      let lr, hr = add (l1, h1) (l2, h2) in
      Range (lr, hr)
  | _ -> Top

let sub i1 i2 =
  match (i1, i2) with
  | Range (l1, h1), Range (l2, h2) ->
      let lr, hr = sub (l1, h1) (l2, h2) in
      Range (lr, hr)
  | _ -> Top

let mul i1 i2 =
  match (i1, i2) with
  | Range (l1, h1), Range (l2, h2) ->
      let lr, hr = mul (l1, h1) (l2, h2) in
      Range (lr, hr)
  | _ -> Top

let div i1 i2 =
  match (i1, i2) with
  | Range (l1, h1), Range (l2, h2) ->
      let lr, hr = div (l1, h1) (l2, h2) in
      Range (lr, hr)
  | _ -> Top

let neg = function
  | Top -> Top
  | Range (l, h) ->
      let l', h' = neg (l, h) in
      Range (l', h')

let pow i exp =
  match i with
  | Top -> Top
  | Range (l, h) ->
      let l', h' = pow (l, h) exp in
      Range (l', h')

let root i exp =
  match i with
  | Top -> Some Top
  | Range (l, h) -> (
    match root (l, h) exp with
    | None -> None
    | Some (l', h') -> Some (Range (l', h')) )

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
  let _contains_zero o = subseteq (Range (Q.zero, Q.zero)) o in
  match (meet x (div r y), meet y (div r x)) with
  | Some x, Some y -> Some (x, y)
  | _ -> None

let bwd_div i1 i2 _r : (t * t) option = Some (i1, i2)

let bwd_neg (i : t) (r : t) : t option = meet i (neg r)

let bwd_pow itv i r : t option =
  Option.map (meet itv) (root r i) |> Option.join

(* Guards *)

let filter_leq_range (l1, h1) (l2, h2) :
    ((Q.t * Q.t) * (Q.t * Q.t)) Consistency.t =
  let open Consistency in
  if Q.leq h1 l2 then Sat
  else if Q.gt l1 h2 then Unsat
  else
    let h1' = Q.min h1 h2 and l2' = Q.max l1 l2 in
    Filtered (((l1, h1'), (l2', h2)), l1 = h1' || l2' = h2)

let filter_lt_range ((l1, h1) as i1) ((l2, h2) as i2) :
    ((Q.t * Q.t) * (Q.t * Q.t)) Consistency.t =
  let open Consistency in
  if Q.lt h1 l2 then Sat
  else if (l1 = h1 && i1 = i2) || Q.gt l1 h2 then Unsat
  else
    let h1' = Q.min h1 h2 and l2' = Q.max l1 l2 in
    Filtered (((l1, h1'), (l2', h2)), l1 = h1' || l2' = h2)

let filter_eq_range ((l1, h1) as i1) ((l2, h2) as i2) :
    (Q.t * Q.t) Consistency.t =
  let open Consistency in
  if l1 = h1 && i1 = i2 then Sat
  else
    let l = Q.max l1 l2 and u = Q.min h1 h2 in
    if Q.leq l u then Filtered ((l, u), false) else Unsat

let filter_diseq_range ((l1, h1) as i1) ((l2, h2) as i2) :
    ((Q.t * Q.t) * (Q.t * Q.t)) Consistency.t =
  let open Consistency in
  if Q.equal l1 h1 && Q.equal l2 h2 && Q.equal l1 l2 then Unsat
  else
    let l = Q.max l1 l2 and u = Q.min h1 h2 in
    if Q.leq l u then Filtered ((i1, i2), false) else Sat

(* Guards *)

let filter_leq (i1 : t) (i2 : t) : (t * t) Consistency.t =
  match (i1, i2) with
  | Range (l1, h1), Range (l2, h2) ->
      Consistency.map
        (fun ((l1, h1), (l2, h2)) -> (Range (l1, h1), Range (l2, h2)))
        (filter_leq_range (l1, h1) (l2, h2))
  | Top, Range (l, h) ->
      let r = Range (Q.of_float neg_infinity, h) in
      Filtered ((r, i2), l = h)
  | Range (l, h), Top ->
      let r = Range (l, Q.of_float infinity) in
      Filtered ((i1, r), l = h)
  | _ -> Filtered ((i1, i2), false)

let filter_lt (i1 : t) (i2 : t) : (t * t) Consistency.t =
  match (i1, i2) with
  | Range (l1, h1), Range (l2, h2) ->
      Consistency.map
        (fun ((l1, h1), (l2, h2)) -> (Range (l1, h1), Range (l2, h2)))
        (filter_lt_range (l1, h1) (l2, h2))
  | Top, Range (_l, h) ->
      let r = Range (Q.of_float neg_infinity, h) in
      Filtered ((r, i2), false)
  | Range (l, _), Top ->
      let r = Range (l, Q.of_float infinity) in
      Filtered ((i1, r), false)
  | _ -> Filtered ((i1, i2), false)

let filter_eq (i1 : t) (i2 : t) : t Consistency.t =
  match (i1, i2) with
  | Range (l1, h1), Range (l2, h2) ->
      Consistency.map
        (fun (l, h) -> Range (l, h))
        (filter_eq_range (l1, h1) (l2, h2))
  | Top, x | x, Top -> Filtered (x, false)

let filter_diseq (i1 : t) (i2 : t) : (t * t) Consistency.t =
  match (i1, i2) with
  | Range (l1, h1), Range (l2, h2) ->
      Consistency.map
        (fun ((l1, h1), (l2, h2)) -> (Range (l1, h1), Range (l2, h2)))
        (filter_diseq_range (l1, h1) (l2, h2))
  | _ -> Filtered ((i1, i2), false)

(* compilation *)
let compile i =
  let open Helper in
  match i with
  | Range (inf, sup) ->
      let i = inf |> Q.to_float |> float_ in
      let s = sup |> Q.to_float |> float_ in
      apply_runtime "float_range" [i; s]
  | _ -> exp_id "QCheck.Gen.float"
