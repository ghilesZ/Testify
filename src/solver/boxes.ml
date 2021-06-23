open Migrate_parsetree
open Ast_410
open Helper
open Lang
open Tools

type eval = I of ItvI.t | F of ItvF.t

let eval_int i = I i

let eval_float f = F f

let float2 (x, y) = (F x, F y)

let int2 (x, y) = (I x, I y)

let swap_pair (a, b) = (b, a)

let map_pair f (a, b) = (f a, f b)

let to_float ((l, h) : ItvI.t) = (Q.of_bigint l, Q.of_bigint h)

let to_int ((l, h) : ItvF.t) = (Z.add (Q.to_bigint l) Z.one, Q.to_bigint h)

let coerce_int = function
  | I i -> i
  | F _ -> invalid_arg "found float but was expected of type int"

let coerce_single_int = function
  | I (l, h) ->
      if l = h then l
      else invalid_arg "found interval but was expected singleton"
  | F _ -> invalid_arg "found float but was expected of type int"

let coerce_float = function
  | F f -> f
  | I _ -> invalid_arg "found int but was expected of type float"

let bwd_to_float x r = ItvI.meet (coerce_int x) (to_int (coerce_float r))

let bwd_to_int x r = ItvF.meet (coerce_float x) (to_float (coerce_int r))

let meet x y =
  match (x, y) with
  | I x, I y -> Option.map eval_int (ItvI.meet x y)
  | F x, F y -> Option.map eval_float (ItvF.meet x y)
  | _ -> invalid_arg "type error, should not occur"

let filter_neg x r =
  match x with
  | I x -> Option.map eval_int (ItvI.bwd_neg x (coerce_int r))
  | F x -> Option.map eval_float (ItvF.bwd_neg x (coerce_float r))

let filter_i_f i_f r_f (a : eval) (b : eval) : (eval * eval) Consistency.t =
  match (a, b) with
  | I x1, I x2 -> Consistency.map int2 (i_f x1 x2)
  | F x1, F x2 -> Consistency.map float2 (r_f x1 x2)
  | _ -> invalid_arg "type error, should not occur"

let filter_leq = filter_i_f ItvI.filter_leq ItvF.filter_leq

let filter_lt = filter_i_f ItvI.filter_lt ItvF.filter_lt

let filter_diseq = filter_i_f ItvI.filter_diseq ItvF.filter_diseq

let filter_eq x1 x2 =
  match (x1, x2) with
  | I x1, I x2 -> Consistency.map eval_int (ItvI.filter_eq x1 x2)
  | F x1, F x2 -> Consistency.map eval_float (ItvF.filter_eq x1 x2)
  | _ -> invalid_arg "type error, should not occur"

(* maps each variable to a (non-empty) interval *)
type t = {ints: ItvI.t SMap.t; floats: ItvF.t SMap.t}

let max_range map range_f =
  Option.map
    (SMap.fold
       (fun v i (vo, io) ->
         if range_f i > range_f io then (v, i) else (vo, io))
       map)
    (SMap.min_binding_opt map)

(* float variable with maximal range *)
let max_range_f (a : t) : (string * ItvF.t) option =
  max_range a.floats ItvF.range

(* integer variable with maximal range *)
let max_range_i (a : t) : (string * ItvI.t) option =
  max_range a.ints ItvI.range

let volume_f (a : t) : Z.t =
  SMap.fold (fun _ x v -> Z.mul (ItvF.range x) v) a.floats Z.one

let volume_i (a : t) : Z.t =
  SMap.fold (fun _ x v -> Z.mul (ItvI.range x) v) a.ints Z.one

let volume a = Z.mul (volume_f a) (volume_i a)

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
  | Float f ->
      let qf = Q.of_float f in
      let qfqf = (qf, qf) |> eval_float in
      (AFloat qfqf, qfqf)
  | Binop (e1, o, e2) ->
      let ((_, i1) as b1) = eval a e1 and ((_, i2) as b2) = eval a e2 in
      let r =
        match o with
        | Add -> ItvI.add (coerce_int i1) (coerce_int i2) |> eval_int
        | Sub -> ItvI.sub (coerce_int i1) (coerce_int i2) |> eval_int
        | AddF -> ItvF.add (coerce_float i1) (coerce_float i2) |> eval_float
        | SubF -> ItvF.sub (coerce_float i1) (coerce_float i2) |> eval_float
        | Mul -> ItvI.mul (coerce_int i1) (coerce_int i2) |> eval_int
        | Div -> ItvI.div (coerce_int i1) (coerce_int i2) |> eval_int
        | MulF -> ItvF.mul (coerce_float i1) (coerce_float i2) |> eval_float
        | DivF -> ItvF.div (coerce_float i1) (coerce_float i2) |> eval_float
        | Pow ->
            ItvF.pow (coerce_float i1) (coerce_single_int i2) |> eval_float
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
  | ToInt e ->
      let ((_, i) as b) = eval a e in
      let r = coerce_float i |> to_int |> eval_int in
      (AToInt b, r)
  | ToFloat e ->
      let ((_, i) as b) = eval a e in
      let r = coerce_int i |> to_float |> eval_float in
      (AToFloat b, r)

let rec refine (a : t) e (x : eval) : t =
  match e with
  | AVar v -> update v (Option.get (meet x (find v a))) a
  | AFloat f ->
      ignore
        (eval_float
           (Option.get (ItvF.meet (coerce_float x) (coerce_float f)))) ;
      a
  | AInt i ->
      ignore
        (eval_int (Option.get (ItvI.meet (coerce_int x) (coerce_int i)))) ;
      a
  | ANeg (e1, i1) ->
      refine a e1
        (eval_int (Option.get (ItvI.bwd_neg (coerce_int i1) (coerce_int x))))
  | ANegF (e1, i1) ->
      refine a e1
        (eval_float
           (Option.get (ItvF.bwd_neg (coerce_float i1) (coerce_float x))))
  | ABinop ((e1, i1), o, (e2, i2)) ->
      let j1, j2 =
        match o with
        | Add ->
            ItvI.bwd_add (coerce_int i1) (coerce_int i2) (coerce_int x)
            |> Option.get |> map_pair eval_int
        | Sub ->
            ItvI.bwd_sub (coerce_int i1) (coerce_int i2) (coerce_int x)
            |> Option.get |> map_pair eval_int
        | AddF ->
            ItvF.bwd_add (coerce_float i1) (coerce_float i2) (coerce_float x)
            |> Option.get |> map_pair eval_float
        | SubF ->
            ItvF.bwd_sub (coerce_float i1) (coerce_float i2) (coerce_float x)
            |> Option.get |> map_pair eval_float
        | Pow ->
            ItvF.bwd_pow (coerce_float i1) (coerce_single_int i2)
              (coerce_float x)
            |> Option.get
            |> fun x -> (F x, i2)
        | _ -> failwith "mul div not implemented yet"
      in
      refine (refine a e1 j1) e2 j2
  | AToInt (e, i) ->
      let j = bwd_to_int i x |> Option.get |> eval_float in
      refine a e j
  | AToFloat (e, i) ->
      let j = bwd_to_float i x |> Option.get |> eval_int in
      refine a e j

(* test transfer function. It reduces the domain of the variables in `a`
   according to the constraint `e1 o e2`. *)
let filter (a : t) (e1 : arith) (o : cmp) (e2 : arith) : t Consistency.t =
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

let join (a : t) (b : t) : t =
  let join_opt_i a b =
    match (a, b) with Some a, Some b -> Some (ItvI.join a b) | _ -> None
  in
  let join_opt_f a b =
    match (a, b) with Some a, Some b -> Some (ItvF.join a b) | _ -> None
  in
  { ints= SMap.merge (fun _ -> join_opt_i) a.ints b.ints
  ; floats= SMap.merge (fun _ -> join_opt_f) a.floats b.floats }

let split_along_f (a : t) (v : string) itv : t list =
  if Z.leq (ItvF.range itv) Z.one then failwith "cannot split atom" ;
  let i_list = ItvF.split itv in
  List.fold_left
    (fun acc b -> {a with floats= SMap.add v b a.floats} :: acc)
    [] i_list

let split_along_i (a : t) (v : string) itv : t list =
  if ItvI.range itv = Z.zero then failwith "cannot split atom" ;
  let i = SMap.find v a.ints in
  let i_list = ItvI.split i in
  List.fold_left
    (fun acc b -> {a with ints= SMap.add v b a.ints} :: acc)
    [] i_list

let split (a : t) : t list =
  match (max_range_f a, max_range_i a) with
  | Some (v_f, itv), None -> split_along_f a v_f itv
  | None, Some (v_i, itv) -> split_along_i a v_i itv
  | Some (v_f, i_f), Some (v_i, i_i) ->
      let r_f = ItvF.range i_f in
      let r_i = ItvI.range i_i in
      if Z.gt r_f r_i then split_along_f a v_f i_f
      else split_along_i a v_i i_i
  | None, None -> failwith "cannot split anymore"

let init =
  let i = (Z.of_int min_int, Z.of_int max_int) in
  let f = (Q.of_float min_float, Q.of_float max_float) in
  fun ints floats ->
    { ints= SSet.fold (fun v -> SMap.add v i) ints SMap.empty
    ; floats= SSet.fold (fun v -> SMap.add v f) floats SMap.empty }

let compile (a : t) =
  let instance = ref empty_list_exp in
  let fill comp map =
    SMap.iter
      (fun v i ->
        let value = apply_nolbl (comp i) [exp_id "rs"] in
        let pair = Ast_helper.Exp.tuple [string_ v; value] in
        instance := cons_exp pair !instance)
      map
  in
  fill ItvI.compile a.ints ;
  fill ItvF.compile a.floats ;
  lambda_s "rs" !instance

let print fmt {ints; floats} =
  Format.fprintf fmt "{%a%a}" (SMap.print ItvI.print) ints
    (SMap.print ItvF.print) floats

let to_drawable {ints; floats} =
  let open Picasso in
  let varsi, vi = List.split (SMap.bindings ints) in
  let varsf, vf = List.split (SMap.bindings floats) in
  let ri = List.map (fun (l, u) -> (Z.to_float l, Z.to_float u)) vi in
  let rf = List.map (fun (l, u) -> (Q.to_float l, Q.to_float u)) vf in
  Drawable.of_ranges (varsi @ varsf) (ri @ rf)
