type t = Z.t * Z.t

let join (l1, h1) (l2, h2) = (Z.min l1 l2, Z.max h1 h2)

let meet _a _b = failwith "todo meet"

let float_size (l, h) = Z.sub h l |> Z.to_float

let score _ = failwith "todo score"

let split _ = failwith "split"

let range (a, b) = Z.sub b a |> Z.to_int
