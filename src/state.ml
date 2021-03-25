open Migrate_parsetree
open Ast_410
open Parsetree
open Helper

(* map for type identifiers *)
module Types = Map.Make (struct
  type t = Longident.t

  let compare = compare
end)

(* main type, for rewritting state *)
type state =
  { props: expression Types.t (* constraints*)
  ; gens: expression Types.t (* generators *)
  ; prints: expression Types.t (* printers *) }

let empty_state = {props= Types.empty; gens= Types.empty; prints= Types.empty}

(* for handling of scopes *)
type t = state list

(* intial state *)
let s0 : t =
  let add_id (t : string) (g : string) (p : string) (gens, prints) =
    ( Types.add (lparse t) (exp_id g) gens
    , Types.add (lparse t) (exp_id p) prints )
  in
  let gens, prints =
    (Types.empty, Types.empty)
    |> add_id "unit" "QCheck.Gen.unit" "QCheck.Print.unit"
    |> add_id "bool" "QCheck.Gen.bool" "string_of_bool"
    |> add_id "char" "QCheck.Gen.char" "string_of_char"
    |> add_id "int" "QCheck.Gen.int" "string_of_int"
    |> add_id "float" "QCheck.Gen.float" "string_of_float"
  in
  [{gens; prints; props= Types.empty}]

(* registering functions *)
let register_print (s : t) lid p =
  match s with
  | h :: t -> {h with prints= Types.add lid p h.prints} :: t
  | [] -> assert false

let register_gen s lid g =
  match s with
  | h :: t -> {h with gens= Types.add lid g h.gens} :: t
  | [] -> assert false

let register_prop s lid p =
  match s with
  | h :: t -> {h with props= Types.add lid p h.props} :: t
  | [] -> assert false

exception Found of expression

let browse_scope f s =
  try
    List.iter
      (fun st -> match f st with None -> () | Some e -> raise (Found e))
      s ;
    None
  with Found e -> Some e

(* getters *)
let get_print s lid = browse_scope (fun st -> Types.find_opt lid st.prints) s

let get_gen s lid = browse_scope (fun st -> Types.find_opt lid st.gens) s

let get_prop s lid = browse_scope (fun st -> Types.find_opt lid st.props) s

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

let new_block s : t = empty_state :: s

let end_block = function
  | [] -> invalid_arg "end block on an empty scope"
  | _ :: s -> s
