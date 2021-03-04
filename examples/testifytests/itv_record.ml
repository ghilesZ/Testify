type itv = {inf: int; sup: int} [@@s.t inf <= sup]

let neg ({inf; sup} : itv) : itv = {inf= -sup; sup= -inf}

let add ({inf= low1; sup= high1} : itv) ({inf= low2; sup= high2} : itv) : itv
    =
  {inf= low1 + low2; sup= high1 + high2}
