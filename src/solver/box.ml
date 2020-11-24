open Migrate_parsetree
open Ast_410
open Helper

(* maps each variable to a (non-empty) interval *)
type t = {ints: ItvI.t SMap.t; floats: ItvF.t SMap.t}

let join (a : t) (b : t) : t =
  let join_opt_i a b =
    match (a, b) with Some a, Some b -> Some (ItvI.join a b) | _ -> None
  in
  let join_opt_f a b =
    match (a, b) with Some a, Some b -> Some (ItvF.join a b) | _ -> None
  in
  { ints= SMap.merge (fun _ -> join_opt_i) a.ints b.ints
  ; floats= SMap.merge (fun _ -> join_opt_f) a.floats b.floats }

let meet (a : t) (b : t) : t option =
  let meet_opt_i a b =
    match (a, b) with
    | Some a, Some b -> Some (Option.get (ItvI.meet a b))
    | _ -> None
  in
  let meet_opt_f a b =
    match (a, b) with
    | Some a, Some b -> Some (Option.get (ItvF.meet a b))
    | _ -> None
  in
  try
    Some
      { ints= SMap.merge (fun _ -> meet_opt_i) a.ints b.ints
      ; floats= SMap.merge (fun _ -> meet_opt_f) a.floats b.floats }
  with Invalid_argument _ -> None

(* mesure *)
(* ------ *)

(* float variable with maximal range *)
let max_range_f (a : t) : string * ItvF.t =
  SMap.fold
    (fun v i (vo, io) ->
      if ItvF.float_size i > ItvF.float_size io then (v, i) else (vo, io))
    a.floats
    (SMap.min_binding a.floats)

(* integer variable with minimal (non-nul) range *)
let min_range_i (a : t) : (string * ItvI.t) option =
  match SMap.min_binding a.ints with
  | bind ->
      let k, v =
        SMap.fold
          (fun v i (vo, io) ->
            let o_r = ItvI.range io in
            if ItvI.range i < o_r || o_r = 0 then (v, i) else (vo, io))
          a.ints bind
      in
      if ItvI.range v = 0 then None else Some (k, v)
  | exception Not_found -> None

(* TODO: compute volume for ints *)
let volume_f (a : t) : float =
  SMap.fold (fun _ x v -> ItvF.float_size x *. v) a.floats 1.

let volume_i (a : t) : int =
  SMap.fold (fun _ x v -> ItvI.range x * v) a.ints 1

let volume a = volume_f a *. float (volume_i a)

let filter (_a : t) _constr = failwith "filter box.ml"

let split_along_f (a : t) (v : string) : t list =
  let i = SMap.find v a.floats in
  let i_list = ItvF.split i in
  List.fold_left
    (fun acc b -> {a with floats= SMap.add v b a.floats} :: acc)
    [] i_list

let split_along_i (a : t) (v : string) : t list =
  let i = SMap.find v a.ints in
  let i_list = ItvI.split i in
  List.fold_left
    (fun acc b -> {a with ints= SMap.add v b a.ints} :: acc)
    [] i_list

let split (a : t) : t list =
  let v_f, i_f = max_range_f a in
  match min_range_i a with
  | None -> split_along_f a v_f
  | Some (v_i, i_i) ->
      let r_f = ItvF.float_size i_f in
      if r_f = 0. then split_along_i a v_i
      else if r_f > 1. /. (10. *. float (ItvI.range i_i)) then
        split_along_f a v_f
      else split_along_i a v_i

let init _ _ = failwith "init box"

(* compile an itv into a parsetree expression corresponding to a generator *)
let compile_itv_int ((inf, sup) : ItvI.t) =
  let i = inf |> Z.to_float |> int_of_float |> int_exp in
  let s = sup |> Z.to_float |> int_of_float |> int_exp in
  [exp_id "rs"]
  |> apply_nolbl (apply_runtime "int_range" [i; s])
  |> apply_runtime_1 "mk_int" |> lambda_s "rs"

(* compile an itv into a parsetree expression corresponding to a generator *)
let compile_itv_float ((inf, sup) : ItvF.t) =
  let i = inf |> Q.to_float |> float_exp in
  let s = sup |> Q.to_float |> float_exp in
  [exp_id "rs"]
  |> apply_nolbl (apply_runtime "float_range" [i; s])
  |> apply_runtime_1 "mk_float"
  |> lambda_s "rs"

let compile (a : t) =
  let instance = ref empty_list_exp in
  SMap.iter
    (fun v i ->
      let value = apply_nolbl (compile_itv_int i) [exp_id "rand_state"] in
      let pair = Ast_helper.Exp.tuple [string_exp v; value] in
      instance := cons_exp pair !instance)
    a.ints ;
  SMap.iter
    (fun v i ->
      let value = apply_nolbl (compile_itv_float i) [exp_id "rand_state"] in
      let pair = Ast_helper.Exp.tuple [string_exp v; value] in
      instance := cons_exp pair !instance)
    a.floats ;
  lambda_s "rand_state" !instance
