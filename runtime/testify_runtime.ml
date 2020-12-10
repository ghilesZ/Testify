open QCheck

let holder = ref ([] : Test.t list)

(* test storing management *)
let add_test count name gen pred =
  let t = QCheck.Test.make ~count ~name gen pred in
  holder := t :: !holder

let run_test () =
  let holder = List.rev !holder in
  QCheck_base_runner.run_tests ~colors:true ~long:true ~verbose:true holder

(* abstract generators handling *)
type generable = GInt of int | GFloat of float

let mk_int x = GInt x

let mk_float x = GFloat x

(* Type of random concretizations *)
type instance = (string * generable) list

let get_int name (l : instance) =
  match List.assoc name l with GInt i -> i | _ -> failwith "type error"

let get_float name (l : instance) =
  match List.assoc name l with GFloat f -> f | _ -> failwith "type error"

(* int range generator *)
let int_range a b =
  if b < a then invalid_arg "Gen.int_range" ;
  if a >= 0 || b < 0 then fun st -> a + Gen.int_bound (b - a) st
  else
    fun (* range potentially bigger than max_int: we split on 0 and choose
           the itv wrt to their size ratio *)
          st ->
    let f_a = float_of_int a in
    let ratio = -.f_a /. (1. +. float_of_int b -. f_a) in
    if Random.State.float st 1. <= ratio then
      -Gen.int_bound (-(a + 1)) st - 1
    else Gen.int_bound b st

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
    let r = QCheck.Gen.float_bound_exclusive total_weight rs in
    (aux r gens) rs

let count = ref 1000

let reject pred g = QCheck.find_example ~f:pred ~count:!count g
