open Migrate_parsetree
open Ast_410
open Parsetree

(* map for type identifiers *)
module Types = Map.Make (struct
  type t = Longident.t

  let compare = compare
end)

(* main type, for rewritting state *)
type t =
  { props: expression Types.t (* constraints*)
  ; gens: expression Types.t (* generators *)
  ; prints: expression Types.t (* printers *) }

(* registering functions *)
let register_print s lid p = {s with prints= Types.add lid p s.prints}

let register_gen s lid g = {s with gens= Types.add lid g s.gens}

let register_prop s lid p = {s with props= Types.add lid p s.props}
