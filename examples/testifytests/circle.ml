(* set of 2D points that are within the circle centered in (42,42) of radius
   100 *)
type circle_42 = {x: float; y: float}

(* [@@s.t ((x -. 42.) ** 2.) +. ((y -. 42.) ** 2.) <=. 10000.] *)

let translate ({x; y} : circle_42) (dx : float) (dy : float) : circle_42 =
  {x= x +. dx; y= y +. dy}

let c : circle_42 = {x= 41.; y= 40.}
