open Testify

(* testing few arithmetical properties *)
(***************************************)

(* this function will be used as a generator for the following test *)
let[@gen] int_gen = QCheck.int

(* commutativity and associativity test *)
let[@commut][@assoc] add a b = a + b

(* test that mul is distributive over add *)
let[@commut][@assoc][@distrib add] mul a b = a * b

(* soundiness test for intervals *)
(*********************************)

let print_itv fmt (a,b) =
  Format.fprintf fmt "[%i;%i]" a b

(* rand_gamma tags a function that will be used for soundness test
   it should generate randomly and uniformly a value in \gamma(e) *)
let[@rand_gamma] rec spawn (a,b) =
  assert (a<=b);
  if b = a then a
  else if a >= 0 then (QCheck.Gen.int_range a b) (Random.get_state ())
  else if b <= 0 then - ((QCheck.Gen.int_range (-b) (-a)) (Random.get_state ()))
  else
    let f_a = float a in
    let ratio = (-.f_a) /. (float b -. f_a) in
    if Random.float 1. < ratio then spawn (a,0)
    else spawn (0,b)

(* in_gamma(e,i) <==> i \in \gamma(e). It avoids computing gamma *)
let[@in_gamma] abstracts (a,b) i = a <= i && i <= b

(* setting a generator for itvs *)
let[@gen] gen_itv =
  QCheck.(Gen.(map2 (fun i j -> (min i j),(max i j)) int int)
          |> make ~print:(Format.asprintf "%a" print_itv))

(* test that add_itv is a sound over-approx of add, w.r.t to the GC-ish (spawn,abstracts)*)
let[@over_approx add] add_itv (a1,a2) (b1,b2) =
  (a1+b1),(a2+b2)
