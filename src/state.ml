open Helper

(* map for type identifiers *)
module Env = Map.Make (struct
  type t = Longident.t

  let compare = compare
end)

type t = Typrepr.t Env.t

let empty = Env.empty

(* intial state *)
let s0 : t =
  let add_id (t : string) = Env.add (lparse t) in
  Env.empty
  |> add_id "unit" Typrepr.unit
  |> add_id "bool" Typrepr.bool
  |> add_id "char" Typrepr.char
  |> add_id "int" Typrepr.int
  |> add_id "float" Typrepr.float

(* registering functions *)
let register_print (s : t) lid p =
  Env.update lid
    (function
      | None -> Some Typrepr.(add_printer empty p)
      | Some info -> Some Typrepr.(add_printer info p))
    s

let register_gen (s : t) lid g =
  Env.update lid
    (function
      | None -> Some Typrepr.(add_generator empty g)
      | Some info -> Some Typrepr.(add_generator info g))
    s

let register_prop (s : t) lid spec =
  Env.update lid
    (function
      | None -> Some Typrepr.(add_specification empty spec)
      | Some info -> Some Typrepr.(add_specification info spec))
    s

(* getters *)

let get = Env.find_opt

let get_print s lid = Option.bind (Env.find_opt lid s) Typrepr.get_printer

let get_gen s lid = Option.bind (Env.find_opt lid s) Typrepr.get_generator

let get_prop s lid =
  Option.bind (Env.find_opt lid s) Typrepr.get_specification

(* updates a state according to a gen option, a print opt and a prop opt *)
let update s id (gen, print, prop) =
  let s = Option.(value ~default:s (map (register_gen s id) gen)) in
  let s = register_print s id print in
  Option.(value ~default:s (map (register_prop s id) prop))

(* TODO: make sure no name conflict can occur *)
let register_param s ct =
  let txt = typ_var_of_ct ct in
  let lid = lparse txt in
  let exp = exp_id txt in
  let s = register_gen s lid exp in
  let s = register_print s lid exp in
  register_prop s lid exp
