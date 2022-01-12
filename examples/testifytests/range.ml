type range = {low: int; high: int} [@@s.t low <= high]

let neg (r : range) : range = {low= -r.low; high= -r.high - 100}
