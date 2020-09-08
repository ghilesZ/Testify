open Testify_lib

type point = int * int

let dist (p1:point) (p2:point) : pos_int =
  let x1,y1=p1 in
  let x2,y2=p2 in
  let dx = x1 - x2 and dy = y1 - y2 in
  dx * dx + dy * dy
