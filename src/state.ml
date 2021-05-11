open Migrate_parsetree
open Ast_410
open Parsetree
open Helper

(* map for long identifiers *)
module Env = Map.Make (struct
  type t = Longident.t

  let compare = compare
end)

type t = {types: Typrepr.t Env.t; params: Typrepr.param Env.t}

let get_env (typconstr : Typrepr.param) (args : Typrepr.t list) =
  List.combine typconstr.vars args

let get_param l s = Env.find_opt l s.params

let empty = {types= Env.empty; params= Env.empty}

(* intial state *)
let s0 : t =
  let add_id (id : string) repr s =
    {s with types= Env.add (lparse id) repr s.types}
  in
  let add_param_td (id : string) p s =
    {s with params= Env.add (lparse id) p s.params}
  in
  empty
  |> add_id "unit" Typrepr.unit
  |> add_id "bool" Typrepr.bool
  |> add_id "char" Typrepr.char
  |> add_id "int" Typrepr.int
  |> add_id "float" Typrepr.float
  |> add_param_td "option" Typrepr.option_
  |> add_param_td "ref" Typrepr.ref_
  |> add_param_td "result" Typrepr.result_

(* registering functions *)
let register_print (s : t) lid p =
  { s with
    types=
      Env.update lid
        (function
          | None -> Some Typrepr.(add_printer empty p)
          | Some info -> Some Typrepr.(add_printer info p))
        s.types }

let register_gen (s : t) lid g =
  { s with
    types=
      Env.update lid
        (function
          | None -> Some Typrepr.(add_generator empty g)
          | Some info -> Some Typrepr.(add_generator info g))
        s.types }

let register_prop (s : t) lid spec =
  { s with
    types=
      Env.update lid
        (function
          | None -> Some Typrepr.(add_specification empty spec)
          | Some info -> Some Typrepr.(add_specification info spec))
        s.types }

(* getters *)

let get lid s = Env.find_opt lid s.types

let update s id infos = {s with types= Env.add id infos s.types}

let update_param s id td =
  let extract_var ct =
    match ct.ptyp_desc with Ptyp_var var -> var | _ -> raise Exit
  in
  try
    let vars =
      List.map (fun (ct, _variance) -> extract_var ct) td.ptype_params
    in
    let open Typrepr in
    let param = {vars; body= td} in
    {s with params= Env.add id param s.params}
  with Exit -> s
