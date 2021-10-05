type t = (string * State.t) list

let s0 = [("stdlib", State.s0)]

let empty name = [(name, State.empty)]

let begin_ (states : t) name : t = (name, State.empty) :: states

let end_ = function
  | (name, state) :: (name', state') :: tl ->
      let parent = (name', State.join (State.end_scope name state) state') in
      parent :: tl
  | _ -> invalid_arg "no module to end in scope"

let get lid s =
  let rec find lid scopes =
    match scopes with
    | [] -> None
    | (_, h) :: tl -> (
      match State.get lid h with None -> find lid tl | x -> x )
  in
  find lid s

let get_param lid s =
  let rec find lid scopes =
    match scopes with
    | [] -> None
    | (_, h) :: tl -> (
      match State.get_param lid h with None -> find lid tl | x -> x )
  in
  find lid s

let update (s : t) id infos =
  match s with
  | (name, h) :: tl -> (name, State.update h id infos) :: tl
  | [] -> invalid_arg "no module in scope"

let update_param (s : t) id td =
  match s with
  | (name, h) :: tl -> (name, State.update_param h id td) :: tl
  | [] -> invalid_arg "no module in scope"
