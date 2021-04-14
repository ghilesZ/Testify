open Migrate_parsetree
open Ast_410
open Parsetree
open Helper

(* map for type identifiers *)
module Types = Map.Make (struct
  type t = Longident.t

  let compare = compare
end)

type info =
  { printer: expression option
  ; generator: expression option
  ; specification: expression option
  ; cardinality: Z.t option }

(* main type, for rewritting state *)
type t =
  { props: expression Types.t (* constraints*)
  ; gens: expression Types.t (* generators *)
  ; prints: expression Types.t (* printers *) }

let empty_state = {props= Types.empty; gens= Types.empty; prints= Types.empty}

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
  {gens; prints; props= Types.empty}

(* registering functions *)
let register_print (s : t) lid p = {s with prints= Types.add lid p s.prints}

let register_gen s lid g = {s with gens= Types.add lid g s.gens}

let register_prop s lid p = {s with props= Types.add lid p s.props}

exception Found of expression

(* getters *)
let get_print s lid = Types.find_opt lid s.prints

let get_gen s lid = Types.find_opt lid s.gens

let get_prop s lid = Types.find_opt lid s.props

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
