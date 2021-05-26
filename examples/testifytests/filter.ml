(* Second-order digital-filter program *)

type box2 = float * float
[@@satisfying fun (x, y) -> -2. <. x && x <. 2. && -2. <. y && y <. 2.]

let noise () = Random.float 0.2 -. 0.1

let transform () : box2 =
  let rec aux n (a, b) =
    let r = (1.5 *. a) -. (0.7 *. b) +. noise () in
    if n = 0 then (r, a) else aux (n - 1) (r, a)
  in
  aux 1000 (noise (), noise ())
