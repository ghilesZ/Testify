type t = Z.t * Z.t

let z2 = Z.of_int 2

let join (l1, h1) (l2, h2) = (Z.min l1 l2, Z.max h1 h2)

let meet (l1, h1) (l2, h2) : t option =
  let low = Z.max l1 l2 in
  let high = Z.min h1 h2 in
  if Z.gt low high then None else Some (low, high)

let range (a, b) = Z.sub b a |> Z.to_int

let split (l, h) =
  if l = h then invalid_arg "split"
  else
    let mid = Z.add l (Z.div (Z.sub h l) z2) in
    [(l, mid); (Z.add mid Z.one, h)]

(* Forward operators *)

let add (l1, h1) (l2, h2) = (Z.add l1 l2, Z.add h1 h2)

let sub (l1, h1) (l2, h2) = (Z.sub l1 h2, Z.sub h1 l2)

let neg (l1, h1) = (Z.neg h1, Z.neg l1)

(* Backward operators *)

let merge_bot2 x y =
  match (x, y) with
  | None, _ | _, None -> None
  | Some a, Some b -> Some (a, b)

let bwd_add i1 i2 r : (t * t) option =
  merge_bot2 (meet i1 (sub r i2)) (meet i2 (sub r i1))

let bwd_sub (i1 : t) (i2 : t) (r : t) : (t * t) option =
  merge_bot2 (meet i1 (add i2 r)) (meet i2 (sub i1 r))
