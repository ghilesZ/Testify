type t = Q.t * Q.t

let join (l1,h1) (l2,h2) = Q.min l1 l2, Q.max h1 h2

let meet _a _b = failwith "todo meet"

let float_size (l,h) = Q.sub h l |> Q.to_float

let score _ = failwith "todo score"

let split _ = failwith "split"
