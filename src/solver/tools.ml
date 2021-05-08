module SSet = Set.Make (String)
module SMap = Map.Make (String)

let n_first l n =
  let rec loop acc n = function
    | [] -> invalid_arg "Tools.n_first: not enough elements in list"
    | h :: tl -> if n > 0 then loop (h :: acc) (n - 1) tl else List.rev acc
  in
  loop [] n l
