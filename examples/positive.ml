type p_int = int [@satisfying (fun x -> x >= 0)]

let fact (n:p_int) : p_int =
  let rec aux acc = function
    | 0 | 1 -> acc
    | n -> aux (n*acc) (n-1)
  in
  aux 1 n
