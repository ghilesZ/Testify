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
  | Approached q -> Format.fprintf fmt "~%a" Q.pp_print q

let map2 fz fq c1 c2 =
  match (c1, c2) with
  | Exact c1, Exact c2 -> Exact (fz c1 c2)
  | Exact c1, Approached c2 | Approached c2, Exact c1 ->
      let c1 = Q.of_bigint c1 in
      Approached (fq c1 c2)
  | Approached c1, Approached c2 -> Approached (fq c1 c2)

let sum = map2 Z.add Q.add

let product = map2 Z.mul Q.mul

let sub = map2 Z.mul Q.mul
