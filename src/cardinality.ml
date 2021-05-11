type t = Exact of Z.t | Approached of Q.t

let print_exact =
  let z12 = Z.of_int 4096 in
  let close_log fmt z =
    let down = Z.log2 z in
    let up = Z.log2 z in
    let two = Z.of_int 2 in
    if z = Z.shift_left two down then
      Format.fprintf fmt "2<sup>%i</sup>" down
    else if Z.sub z (Z.shift_left two down) < Z.sub (Z.shift_left two up) z
    then Format.fprintf fmt "~2<sup>%i</sup>" down
    else Format.fprintf fmt "~2<sup>%i</sup>" up
  in
  fun fmt z ->
    if Z.gt z z12 then close_log fmt z
    else Format.fprintf fmt "%a" Z.pp_print z

let print fmt = function
  | Exact z -> print_exact fmt z
  | Approached q -> Format.fprintf fmt "%a (estimation)" Q.pp_print q

let sum c1 c2 =
  match (c1, c2) with
  | Exact c1, Exact c2 -> Exact (Z.add c1 c2)
  | Exact c1, Approached c2 | Approached c2, Exact c1 ->
      let c1 = Q.of_bigint c1 in
      Approached (Q.add c1 c2)
  | Approached c1, Approached c2 -> Approached (Q.add c1 c2)

let product c1 c2 =
  match (c1, c2) with
  | Exact c1, Exact c2 -> Exact (Z.mul c1 c2)
  | Exact c1, Approached c2 | Approached c2, Exact c1 ->
      let c1 = Q.of_bigint c1 in
      Approached (Q.mul c1 c2)
  | Approached c1, Approached c2 -> Approached (Q.mul c1 c2)
