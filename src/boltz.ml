open Arbogen

type t = {spec: string Grammar.expression; aux_rules: Frontend.ParseTree.t}

(** {2 Getters} *)

let spec {spec; _} = spec

let aux_rules {aux_rules; _} = aux_rules

(** {2 Base cases and combinators} *)

let epsilon = {spec= Grammar.Z 0; aux_rules= []}

let z = {spec= Grammar.Z 1; aux_rules= []}

let ref name = {spec= Grammar.Ref name; aux_rules= []}

let product args =
  { spec= List.map spec args |> Grammar.product
  ; aux_rules= List.map aux_rules args |> List.flatten }

let union args =
  { spec= List.map spec args |> Grammar.union
  ; aux_rules= List.map aux_rules args |> List.flatten }

let indirection name boltz =
  {spec= Grammar.Ref name; aux_rules= (name, boltz.spec) :: boltz.aux_rules}

(** {2 Conversion} *)

let as_grammar name {spec; aux_rules} = (name, spec) :: aux_rules

(** {2 Pretty printing} *)

let pp fmt {spec; aux_rules} =
  Arbogen.Grammar.pp_expression ~pp_ref:Format.pp_print_string fmt spec ;
  match aux_rules with
  | [] -> ()
  | _ ->
      Format.fprintf fmt "\nwhere:\n%a" Arbogen.Frontend.ParseTree.pp
        aux_rules

let markdown fmt = Format.fprintf fmt "```\n%a\n```\n" pp
