type t = int * int [@satisfying (fun (a,b) -> a < b)]

let mk (a:int) (b:int) : t = a,b

let add ((l1,u1):t) ((l2,u2):t) : t =
  (l1+l2),(u1+u2)
