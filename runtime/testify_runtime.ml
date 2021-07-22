let tests = ref ([] : QCheck.Test.t list)

(* test storing management *)
let add_fun count name print gen pred =
  let arb = QCheck.make ~print gen in
  let t = QCheck.Test.make ~count ~name arb pred in
  tests := t :: !tests

let add_const count name pred =
  let arb = QCheck.make QCheck.Gen.unit in
  let t = QCheck.Test.make ~count ~name arb pred in
  tests := t :: !tests

let run_test () =
  List.rev !tests
  |> QCheck_base_runner.run_tests ~colors:true ~verbose:true
  |> ignore

let set_seed = QCheck_base_runner.set_seed

(* input -> output utilities *)
let opt_pred pred = function None -> true | Some x -> pred x

let opt_gen g rs =
  try Some (g rs)
  with Invalid_argument _ | QCheck.No_example_found _ -> None

let opt_print p = function
  | Some x -> p x
  | None -> invalid_arg "should not occur"

let sat_output pred = function None -> true | Some (out, _) -> pred out

(* abstract generators handling *)
type generable = GInt of int | GFloat of float

let mk_int x = GInt x

let mk_float x = GFloat x

let to_int = function GInt i -> i | _ -> failwith "type error"

let to_float = function GFloat f -> f | _ -> failwith "type error"

(* Type of random concretizations *)
type instance = (string * generable) list

let get_int name (l : instance) = List.assoc name l |> to_int

let get_float name (l : instance) = List.assoc name l |> to_float

(* GENERATORS *)

let unit = QCheck.Gen.unit

let int_range = QCheck.Gen.int_range

(* float range generator *)
let float_range a b =
  if b < a then
    let msg = Format.asprintf "[%f;%f]" a b in
    invalid_arg ("invalid float_range: " ^ msg)
  else if a >= 0. || b <= 0. then fun st ->
    a +. QCheck.Gen.float_bound_inclusive (b -. a) st
  else
    fun (* range potentially bigger than max_float: we split on 0 and choose
           the itv wrt to their size ratio *)
          st ->
    let ratio = -.a /. (b -. a) in
    if Random.State.float st 1. < ratio then
      -.QCheck.Gen.float_bound_inclusive (-.a) st
    else QCheck.Gen.float_bound_inclusive b st

let mk_float_range down up rs = float_range down up rs |> mk_float

let mk_int_range down up rs = int_range down up rs |> mk_int

(* builds a generator from a list of weighted generators *)
let weighted (gens : (float * 'a QCheck.Gen.t) list) : 'a QCheck.Gen.t =
  let total_weight = List.fold_left (fun acc (w, _) -> acc +. w) 0. gens in
  let rec aux cpt = function
    | [] -> assert false
    | [(_, x)] -> x
    | (w, g) :: tl ->
        let cpt = cpt -. w in
        if cpt < 0. then g else aux cpt tl
  in
  fun rs ->
    let r = QCheck.Gen.float_bound_exclusive total_weight rs in
    (aux r gens) rs

let count = ref 1000

let reject pred g = QCheck.find_example ~f:pred ~count:!count g

(* point obtained by translation of f1 by r*f1f2, r in [0;1]. FIXME: uniform
   for reals but not for floats *)
let barycenter_f r f1 f2 = ((1. -. r) *. f1) +. (r *. f2)

(* same as barycenter_f using integers *)
let barycenter_i r i1 i2 =
  ((1. -. r) *. float i1) +. (r *. float i2) |> int_of_float

(* Polyhedra primitives *)
let f_vec r i1 i2 =
  List.map2
    (fun (v1, i1) (_, i2) ->
      match (i1, i2) with
      | GInt i1, GInt i2 -> (v1, GInt (barycenter_i r i1 i2))
      | GFloat f1, GFloat f2 -> (v1, GFloat (barycenter_f r f1 f2))
      | _ ->
          Format.asprintf "Type mismatch for variable %s" v1 |> invalid_arg)
    i1 i2

(* translation of i1 by r1*i1v1, r2*i1v2 ... rn*i1vn where r1 .. rn are
   random coeff in [0;1] *)
let translate g1 (r : float list) vecs =
  List.fold_left2 (fun p r v -> f_vec r p v) g1 r vecs

let simplex (x : instance) (vectors : instance list) (nb_dim : int) seed =
  let sum = ref 0. in
  let random_vecs =
    List.rev_map
      (fun _ ->
        let r = QCheck.Gen.float_bound_inclusive 1. seed in
        sum := !sum +. r ;
        r)
      vectors
  in
  translate x
    ( if !sum > (nb_dim |> float) /. 2. then
      List.rev_map (fun f -> 1. -. f) random_vecs
    else List.rev random_vecs )
    vectors

(* Redefinition of some operators to explicit types in constraints *)

let ( <=. ) : float -> float -> bool = ( <= )

let ( <. ) : float -> float -> bool = ( < )

let ( >. ) : float -> float -> bool = ( > )

let ( >=. ) : float -> float -> bool = ( >= )

let ( =. ) : float -> float -> bool = ( = )

let ( <>. ) : float -> float -> bool = ( <> )

let ( <= ) : int -> int -> bool = ( <= )

let ( < ) : int -> int -> bool = ( < )

let ( > ) : int -> int -> bool = ( > )

let ( >= ) : int -> int -> bool = ( >= )

let ( = ) : int -> int -> bool = ( = )

let ( <> ) : int -> int -> bool = ( <> )

(* Benchmarking stuff *)
let speed_estimate nb gen =
  let st = Random.get_state () in
  let start = Unix.gettimeofday () in
  for _ = 0 to nb do
    let _ = gen st in
    ()
  done ;
  let ending = Unix.gettimeofday () in
  let elapsed = ending -. start in
  int_of_float (float nb /. elapsed)
