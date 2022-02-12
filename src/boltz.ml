open Arbogen

(** Combinatorial description of a type *)
type t =
  { spec: string Grammar.expression  (** Main specification of the type *)
  ; aux_rules: Frontend.ParseTree.t
        (** Auxilliary rules that can be used by the main specification e.g.
            for recursive specs *) }

(** {2 Base cases and combinators} *)

let epsilon = {spec= Grammar.Z 0; aux_rules= []}

let z = {spec= Grammar.Z 1; aux_rules= []}

let ref name = {spec= Grammar.Ref name; aux_rules= []}

let product = function
  | [] -> invalid_arg "Boltz.product: empty product"
  | [x] -> x
  | args ->
      { spec= List.map (fun b -> b.spec) args |> Grammar.product
      ; aux_rules= List.map (fun b -> b.aux_rules) args |> List.flatten }

let union = function
  | [] -> invalid_arg "Boltz.union: empty union"
  | [x] -> x
  | args ->
      { spec= List.map (fun b -> b.spec) args |> Grammar.union
      ; aux_rules= List.map (fun b -> b.aux_rules) args |> List.flatten }

let indirection name boltz =
  {spec= Grammar.Ref name; aux_rules= (name, boltz.spec) :: boltz.aux_rules}

(** {2 Conversion} *)

let as_grammar name {spec; aux_rules} = (name, spec) :: aux_rules

module Printer = struct
  open Migrate_parsetree
  open Ast_410
  open Parsetree
  open Helper

  let array printer a =
    Ast_helper.Exp.array (a |> Array.to_list |> List.map printer)

  let rec expr (r : Boltzmann.WeightedGrammar.expression) =
    let loc = !Helper.current_loc in
    match r with
    | Z n -> [%expr Z [%e int_ n]]
    | Product args -> [%expr Product [%e list_of_list (List.map expr args)]]
    | Union args ->
        let args =
          args
          |> List.map (fun (w, e) -> [%expr [%e float_ w], [%e expr e]])
          |> list_of_list
        in
        [%expr Union [%e args]]
    | Seq (w, x) -> [%expr Seq ([%e float_ w], [%e expr x])]
    | Ref id -> [%expr Ref [%e int_ id]]

  let weighted_grammar (wg : Boltzmann.WeightedGrammar.t) =
    let loc = !current_loc in
    [%expr
      Arbogen.Boltzmann.WeightedGrammar.
        {names= [%e array string_ wg.names]; rules= [%e array expr wg.rules]}]
end

let compile (rules : Frontend.ParseTree.t) =
  let grammar =
    rules |> Frontend.ParseTree.completion |> Frontend.ParseTree.to_grammar
  in
  let oracle = Boltzmann.Oracle.Naive.make_expectation 30 grammar in
  let wg = Boltzmann.WeightedGrammar.of_grammar oracle grammar in
  Printer.weighted_grammar wg

(** {2 Pretty printing} *)

let pp fmt {spec; aux_rules} =
  Arbogen.Grammar.pp_expression ~pp_ref:Format.pp_print_string fmt spec ;
  match aux_rules with
  | [] -> ()
  | _ ->
      Format.fprintf fmt "\nwhere:\n%a" Arbogen.Frontend.ParseTree.pp
        aux_rules

let markdown fmt = Format.fprintf fmt "\n```\n%a\n```\n" pp
