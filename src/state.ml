open Migrate_parsetree
open Ast_410
open Parsetree
open Helper

(* map for type identifiers *)
module Types = Map.Make (struct
  type t = Longident.t

  let compare = compare
end)

module Info = struct
  type t =
    { generator: expression option
    ; specification: expression option
    ; cardinality: Z.t option
    ; printer: expression option }

  let get_generator p = p.generator

  let get_specification p = p.specification

  let get_cardinality p = p.cardinality

  let get_printer p = p.printer

  let empty =
    {generator= None; specification= None; cardinality= None; printer= None}

  let add_printer info p = {info with printer= Some p}

  let add_generator info g = {info with generator= Some g}

  let add_specification info s = {info with specification= Some s}

  let free g c p =
    { printer= Some p
    ; generator= Some g
    ; specification= None
    ; cardinality= Some c }

  let constrained g s c p =
    { printer= Some p
    ; generator= Some g
    ; specification= Some s
    ; cardinality= Some c }

  let unit =
    free (exp_id "QCheck.Gen.unit") Z.one (exp_id "QCheck.Print.unit")

  let bool =
    free (exp_id "QCheck.Gen.bool") (Z.of_int 2) (exp_id "string_of_bool")

  let char =
    free (exp_id "QCheck.Gen.char") (Z.of_int 256) (exp_id "string_of_char")

  let int =
    free (exp_id "QCheck.Gen.int")
      (Z.pow (Z.of_int 2) Sys.int_size)
      (exp_id "string_of_int")

  let float =
    free
      (exp_id "QCheck.Gen.float")
      (Z.pow (Z.of_int 2) Sys.int_size)
      (exp_id "string_of_float")
end

type t = Info.t Types.t

(* (\* main type, for rewritting state *\)
 * type t =
 *   { props: expression Types.t (\* constraints*\)
 *   ; gens: expression Types.t (\* generators *\)
 *   ; prints: expression Types.t (\* printers *\) } *)

let empty = Types.empty

(* intial state *)
let s0 : t =
  let add_id (t : string) = Types.add (lparse t) in
  Types.empty |> add_id "unit" Info.unit |> add_id "bool" Info.bool
  |> add_id "char" Info.char |> add_id "int" Info.int
  |> add_id "float" Info.float

(* registering functions *)
let register_print (s : t) lid p =
  Types.update lid
    (function
      | None -> Some Info.(add_printer empty p)
      | Some info -> Some Info.(add_printer info p))
    s

let register_gen (s : t) lid g =
  Types.update lid
    (function
      | None -> Some Info.(add_generator empty g)
      | Some info -> Some Info.(add_generator info g))
    s

let register_prop (s : t) lid spec =
  Types.update lid
    (function
      | None -> Some Info.(add_specification empty spec)
      | Some info -> Some Info.(add_specification info spec))
    s

(* getters *)

let get = Types.find_opt

let get_print s lid = Option.bind (Types.find_opt lid s) Info.get_printer

let get_gen s lid = Option.bind (Types.find_opt lid s) Info.get_generator

let get_prop s lid =
  Option.bind (Types.find_opt lid s) Info.get_specification

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
