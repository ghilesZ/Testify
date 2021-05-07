open QCheck

let tests = ref ([] : Test.t list)

(* test storing management *)
let add_fun count name print gen pred =
  let arb = make ~print gen in
  let t = Test.make ~count ~name arb pred in
  tests := t :: !tests

let add_const count name pred =
  let arb = make Gen.unit in
  let t = Test.make ~count ~name arb pred in
  tests := t :: !tests

let run_test () =
  List.rev !tests |>
  QCheck_base_runner.run_tests ~colors:true ~verbose:true |> ignore

let set_seed = QCheck_base_runner.set_seed

(* input -> output utilities *)
let opt_pred pred = function None -> true | Some x -> pred x

let opt_gen g rs =
  try Some (g rs)
  with Invalid_argument _ | No_example_found _ -> None

let opt_print p = function
  | Some x -> p x
  | None -> invalid_arg "should not occur"

let sat_output pred = function
  | None -> true | Some (out,_) -> pred out

(* abstract generators handling *)
type generable = GInt of int | GFloat of float

let mk_int x = GInt x

let mk_float x = GFloat x

let to_int = function GInt i -> i | _ -> failwith "type error"

let to_float = function GFloat f -> f | _ -> failwith "type error"

(* Type of random concretizations *)
type instance = (string * generable) list

let get_int name (l : instance) =
  List.assoc name l |> to_int

let get_float name (l : instance) =
   List.assoc name l |> to_float

(* GENERATORS *)

let unit = Gen.unit
let int_range = Gen.int_range

(* float range generator *)
let float_range a b =
  if b < a then
    let msg = Format.asprintf "[%f;%f]" a b in
    invalid_arg ("invalid float_range: " ^ msg)
  else if a >= 0. || b <= 0. then fun st ->
    a +. Gen.float_bound_inclusive (b -. a) st
  else
    fun (* range potentially bigger than max_float: we split on 0 and choose
           the itv wrt to their size ratio *)
          st ->
    let ratio = -.a /. (b -. a) in
    if Random.State.float st 1. < ratio then
      -.Gen.float_bound_inclusive (-.a) st
    else Gen.float_bound_inclusive b st

let mk_float_range down up rs =
  float_range down up rs |> mk_float

let mk_int_range down up rs =
  int_range down up rs |> mk_int

(* builds a generator from a list of weighted generators *)
let weighted (gens : (float * 'a Gen.t) list) : 'a Gen.t =
  let total_weight = List.fold_left (fun acc (w, _) -> acc +. w) 0. gens in
  let rec aux cpt = function
    | [] -> assert false
    | (w, g) :: tl ->
       let cpt = cpt -. w in
       if cpt < 0. then g else aux cpt tl
  in
  fun rs ->
    let r = Gen.float_bound_exclusive total_weight rs in
    (aux r gens) rs

let count = ref 1000

let reject pred g =
  find_example ~f:pred ~count:!count g

(* Polyhedra primitives *)
let rint i1 i2 seed =
  let down,up = if i1 < i2 then i1,i2 else i2,i1 in
  int_range down up seed

let rfloat f1 f2 seed =
  let down,up = if f1 < f2 then f1,f2 else f2,f1 in
  float_range down up seed

(* translation of i1 by r*i2 where r is a random factor in [0;1] *)
let vec i1 i2 seed : instance =
  List.map2 (fun (v1,i1) (v2,i2) ->
      if v1 = v2 then
        match i1,i2 with
        | GInt i1, GInt i2 -> v1,GInt (rint i1 i2 seed)
        | GFloat f1, GFloat f2 -> v1,GFloat (rfloat f1 f2 seed)
        | _ -> Format.asprintf "Type mismatch for variable %s" v1
               |> invalid_arg
      else Format.asprintf "Wrong order for variables %s and %s" v1 v2
           |> invalid_arg
    ) i1 i2

let random_generable (x:instance) (ys:instance list) seed =
  List.fold_left (fun i1 i2 -> vec i1 i2 seed) x ys

let (<=.) : float -> float -> bool = (<=)
let (<.)  : float -> float -> bool = (<)
let (>.)  : float -> float -> bool = (>)
let (>=.)  : float -> float -> bool = (>=)
let (=.)  : float -> float -> bool = (=)
let (<>.)  : float -> float -> bool = (<>)

let (<=) : int -> int -> bool = (<=)
let (<)  : int -> int -> bool = (<)
let (>)  : int -> int -> bool = (>)
let (>=)  : int -> int -> bool = (>=)
let (=)  : int -> int -> bool = (=)
let (<>)  : int -> int -> bool = (<>)
