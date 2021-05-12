module SSet = Set.Make (String)

module SMap = struct
  include Map.Make (String)

  let print print_val fmt m =
    Format.pp_print_list
      ~pp_sep:(fun fmt () -> Format.fprintf fmt "; ")
      (fun fmt (key, value) ->
        Format.fprintf fmt "%s: %a" key print_val value)
      fmt (bindings m)
end

let n_first l n =
  let rec loop acc n = function
    | [] -> invalid_arg "Tools.n_first: not enough elements in list"
    | h :: tl -> if n > 0 then loop (h :: acc) (n - 1) tl else List.rev acc
  in
  loop [] n l
