(** This module is a wrapper around the module state that handles the scoping
    rules of OCaml modules *)

(*TODO: open, aliases, includes *)

type t = (string * State.t) list

let print_module fmt (name, state) =
  Format.fprintf fmt "module:%s\n%a\n" name State.print state

let print = Format.pp_print_list print_module

let s0 = [("stdlib", State.s0)]

let empty name = [(name, State.empty)]

let begin_ (states : t) name : t =
  let name = Helper.capitalize_first_char name in
  Log.print "## Begining of module %s\n" name ;
  (name, State.empty) :: states

let end_ = function
  | (name, state) :: (name', state') :: tl ->
      Log.print "## End of module %s\n" name ;
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

let join (e1 : Typrepr.param State.Env.t) (e2 : Typrepr.param State.Env.t) =
  State.(Env.fold Env.add e1 e2)

let get_all_params (s : t) =
  List.fold_left
    (fun acc (_, m) -> join m.State.params acc)
    State.Env.empty s
  |> State.Env.bindings |> List.map snd
  |> List.map (fun p -> p.Typrepr.body)

let update (s : t) id infos =
  match s with
  | (name, h) :: tl -> (name, State.update h id infos) :: tl
  | [] -> invalid_arg "no module in scope"

let update_param (s : t) id td =
  match s with
  | (name, h) :: tl -> (name, State.update_param h id td) :: tl
  | [] -> invalid_arg "no module in scope"
