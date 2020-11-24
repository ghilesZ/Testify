open Migrate_parsetree
open Ast_410
open Helper
open Lang

type eval = I of ItvI.t | F of ItvF.t

let eval_int i = I i

let eval_float f = F f

let real2 (x, y) = (F x, F y)

let int2 (x, y) = (I x, I y)

let swap_pair (a, b) = (b, a)

let to_float ((l, h) : ItvI.t) = (Q.of_bigint l, Q.of_bigint h)

let to_int ((l, h) : ItvF.t) = (Z.add (Q.to_bigint l) Z.one, Q.to_bigint h)

let coerce_int = function
  | I i -> i
  | F _ -> invalid_arg "found float but was expected of type int"

let coerce_float = function
  | F f -> f
  | I _ -> invalid_arg "found int but was expected of type float"

let meet x y =
  match (x, y) with
  | I x, I y -> Option.map eval_int (ItvI.meet x y)
  | F x, F y -> Option.map eval_float (ItvF.meet x y)
  | _ -> invalid_arg "type error, should not occur"

let filter_neg x r =
  match x with
  | I x -> Option.map eval_int (ItvI.bwd_neg x (coerce_int r))
  | F x -> Option.map eval_float (ItvF.bwd_neg x (coerce_float r))

let filter i_f r_f (x1 : eval) (x2 : eval) : (eval * eval) Consistency.t =
  match (x1, x2) with
  | I x1, I x2 -> Consistency.map int2 (i_f x1 x2)
  | F x1, F x2 -> Consistency.map real2 (r_f x1 x2)
  | _ -> invalid_arg "type error, should not occur"

let filter_leq = filter ItvI.filter_leq ItvF.filter_leq

let filter_lt = filter ItvI.filter_lt ItvF.filter_lt

let filter_eq x1 x2 =
  match (x1, x2) with
  | I x1, I x2 -> Consistency.map eval_int (ItvI.filter_eq x1 x2)
  | F x1, F x2 -> Consistency.map eval_float (ItvF.filter_eq x1 x2)
  | _ -> invalid_arg "type error, should not occur"

let filter_diseq = filter ItvI.filter_diseq ItvF.filter_diseq

(* maps each variable to a (non-empty) interval *)
type t = {ints: ItvI.t SMap.t; floats: ItvF.t SMap.t}

(* mesure *)
(* ------ *)

(* float variable with maximal range *)
let max_range_f (a : t) : string * ItvF.t =
  SMap.fold
    (fun v i (vo, io) ->
      if ItvF.range i > ItvF.range io then (v, i) else (vo, io))
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

let volume_f (a : t) : float =
  SMap.fold (fun _ x v -> ItvF.range x *. v) a.floats 1.

let volume_i (a : t) : int =
  SMap.fold (fun _ x v -> ItvI.range x * v) a.ints 1

let volume a = volume_f a *. float (volume_i a)

let find v a =
  try SMap.find v a.ints |> eval_int
  with Not_found -> SMap.find v a.floats |> eval_float

let update key value a =
  try
    SMap.find key a.ints |> ignore ;
    {a with ints= SMap.add key (coerce_int value) a.ints}
  with Not_found ->
    {a with floats= SMap.add key (coerce_float value) a.floats}

type arith2 =
  | AInt of eval
  | AFloat of eval
  | ABinop of arith_annot * bop * arith_annot
  | ANeg of arith_annot
  | ANegF of arith_annot
  | AToInt of arith_annot
  | AToFloat of arith_annot
  | AVar of string

and arith_annot = arith2 * eval

let rec eval (a : t) : arith -> arith_annot = function
  | Var v ->
      let r = find v a in
      (AVar v, r)
  | Int i ->
      let zi = Z.of_int i in
      let zizi = (zi, zi) |> eval_int in
      (AInt zizi, zizi)
  | Binop (e1, o, e2) ->
      let ((_, i1) as b1) = eval a e1 and ((_, i2) as b2) = eval a e2 in
      let r =
        match o with
        | Add -> ItvI.add (coerce_int i1) (coerce_int i2) |> eval_int
        | Sub -> ItvI.sub (coerce_int i1) (coerce_int i2) |> eval_int
        | AddF -> ItvF.add (coerce_float i1) (coerce_float i2) |> eval_float
        | SubF -> ItvF.sub (coerce_float i1) (coerce_float i2) |> eval_float
        | _ -> failwith "not implemented yet"
      in
      (ABinop (b1, o, b2), r)
  | Neg e ->
      let ((_, i) as b) = eval a e in
      let r = ItvI.neg (coerce_int i) |> eval_int in
      (ANeg b, r)
  | NegF e ->
      let ((_, i) as b) = eval a e in
      let r = ItvF.neg (coerce_float i) |> eval_float in
      (ANeg b, r)
  | _ -> failwith "not implemented yet"

let rec refine (a : t) e (x : eval) : t =
  match e with
  | AVar v -> update v (Option.get (meet x (find v a))) a
  | ANeg (e1, i1) ->
      refine a e1
        (eval_int (Option.get (ItvI.bwd_neg (coerce_int i1) (coerce_int x))))
  | ANegF (e1, i1) ->
      refine a e1
        (eval_float
           (Option.get (ItvF.bwd_neg (coerce_float i1) (coerce_float x))))
  | _ -> failwith "refine not implemented yet"

(* test transfer function. It reduces the domain of the variables in `a`
   according to the constraint `e1 o e2`. *)
let guard (a : t) (e1 : arith) (o : cmp) (e2 : arith) : t Consistency.t =
  let open Lang in
  let (b1, i1), (b2, i2) = (eval a e1, eval a e2) in
  let res =
    match o with
    | Lt -> filter_lt i1 i2
    | Leq -> filter_leq i1 i2
    (* a > b <=> b < a*)
    | Geq -> Consistency.map swap_pair (filter_leq i2 i1)
    | Gt -> Consistency.map swap_pair (filter_lt i2 i1)
    | Diseq -> filter_diseq i1 i2
    | Eq -> Consistency.map (fun x -> (x, x)) (filter_eq i1 i2)
  in
  Consistency.map (fun (j1, j2) -> refine (refine a b1 j1) b2 j2) res

let filter (a : t) constr = failwith "filter box.ml"

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

let split (a : t) : t list =
  let v_f, i_f = max_range_f a in
  match min_range_i a with
  | None -> split_along_f a v_f
  | Some (v_i, i_i) ->
      let r_f = ItvF.range i_f in
      if r_f = 0. then split_along_i a v_i
      else if r_f > 1. /. (10. *. float (ItvI.range i_i)) then
        split_along_f a v_f
      else split_along_i a v_i

let init =
  let i = (Z.of_int min_int, Z.of_int max_int) in
  let f = (Q.of_float min_float, Q.of_float max_float) in
  fun ints floats ->
    { ints= SSet.fold (fun v -> SMap.add v i) ints SMap.empty
    ; floats= SSet.fold (fun v -> SMap.add v f) floats SMap.empty }

let compile (a : t) =
  let instance = ref empty_list_exp in
  let aux comp map =
    SMap.iter
      (fun v i ->
        let value = apply_nolbl (comp i) [exp_id "rs"] in
        let pair = Ast_helper.Exp.tuple [string_exp v; value] in
        instance := cons_exp pair !instance)
      map
  in
  aux ItvI.compile a.ints ;
  aux ItvF.compile a.floats ;
  lambda_s "rs" !instance
