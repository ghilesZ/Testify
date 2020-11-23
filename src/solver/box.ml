open Helper

(* maps each variable to a (non-empty) interval *)
type t = Itv.t SMap.t

let join (a:t) (b:t) : t * bool =
  let join_opt a b =
    match a,b with
    | Some a, Some b -> Some (Itv.join a b)
    | _ -> None
  in
  (SMap.merge (fun _ -> join_opt) a b),false

let meet (a:t) (b:t) : t option =
  let meet_opt a b =
    match a,b with
    | Some a, Some b -> Some (Option.get (Itv.meet a b))
    | _ -> None
  in
  try Some (SMap.merge (fun _ -> meet_opt) a b)
  with Invalid_argument _ -> None

(* predicates *)
(* ---------- *)

(* mesure *)
(* ------ *)

(* variable with maximal range *)
let max_range (a:t) : string * Itv.t =
  SMap.fold
    (fun v i (vo,io) ->
      if (Itv.float_size i) > (Itv.float_size io) then v,i else vo,io
    ) a (SMap.min_binding a)

(* variable with maximal range if real or with minimal if integer *)
let mix_range (a:t) : string * Itv.t =
  SMap.fold
    (fun v i (vo,io) ->
      if (Itv.score i) > (Itv.score io) then v,i else vo,io
    ) a (SMap.min_binding a)

let volume (a:t) : float =
  SMap.fold (fun _ x v -> (Itv.float_size x) *. v) a 1.

let filter (_a:t) _constr = failwith "filter box.ml"

let split_along (a:t) (v:string) : t list =
  let i = SMap.find v a in
  let i_list = Itv.split i in
  List.fold_left (fun acc b ->
      (SMap.add v b a)::acc
    ) [] i_list

let split (a:t) : t list =
  let (v,_) = max_range a in split_along a v

let init _ _ = failwith "init box"

let compile _ = failwith "compile box"
