let tests = ref ([] : QCheck.Test.t list)

(* same as [pp], but in bold blue] *)
let bold_blue x = Format.asprintf "\x1b[34;1m%s\x1b[0m" x

(* same as [pp], but in blue *)
let blue x = Format.asprintf "\x1b[36m%s\x1b[0m" x

(* test storing management *)
let add_fun count id loc print gen pred =
  let name = Format.asprintf "function %s in %s" (bold_blue id) (blue loc) in
  let arb = QCheck.make ~print gen in
  let t = QCheck.Test.make ~count ~name arb pred in
  tests := t :: !tests

let add_const count id loc str pred =
  let name = Format.asprintf "constant %s in %s" (bold_blue id) (blue loc) in
  let print () = str in
  let arb = QCheck.make ~print QCheck.Gen.unit in
  let t = QCheck.Test.make ~count ~name arb pred in
  tests := t :: !tests

let run_test () =
  List.rev !tests
  |> QCheck_base_runner.run_tests ~colors:true ~verbose:true
  |> ignore ;
  tests := []

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
      -.(QCheck.Gen.float_bound_inclusive (-.a) st)
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

module Arbg = struct
  open Arbogen
  open Tree

  let max_try = ref 1_000_000

  let size = ref 10

  let consume = function
    | [] -> invalid_arg "Testify_runtime.consume on emtpy list"
    | h :: tl -> (h, tl)

  type 'a store = 'a list array

  (* modifies in place the store *)
  let consume_store n store =
    let len = Array.length store in
    if len < n then
      Format.asprintf "consume_store %i on store of size %i" n len
      |> invalid_arg
    else
      let nth = store.(n) in
      let value, rest = consume nth in
      store.(n) <- rest ; value

  let to_unit arbg lst rs =
    match arbg with
    | Label ("@collect", []) -> consume_store 0 lst
    | Label (_, []) -> QCheck.Gen.unit rs
    | Label (s, _) -> invalid_arg ("arbogen_to_unit wrong label:" ^ s)
    | Tuple _ -> invalid_arg "arbogen_to_unit, expected label but was tuple"

  let to_bool arbg lst rs =
    match arbg with
    | Label ("@collect", []) -> consume_store 0 lst
    | Label (_, []) -> QCheck.Gen.bool rs
    | Label (s, _) -> invalid_arg ("arbogen_to_bool wrong label:" ^ s)
    | Tuple _ -> invalid_arg "arbogen_to_bool, expected bool but was tuple"

  let to_int arbg lst rs =
    match arbg with
    | Label ("@collect", []) -> consume_store 0 lst
    | Label (_, []) -> QCheck.Gen.int rs
    | Label (s, _) -> invalid_arg ("arbogen_to_int wrong label:" ^ s)
    | Tuple _ -> invalid_arg "arbogen_to_int, expected int but was tuple"

  let to_float arbg lst rs =
    match arbg with
    | Label ("@collect", []) -> consume_store 0 lst
    | Label (_, []) -> QCheck.Gen.float rs
    | Label (s, _) -> invalid_arg ("arbogen_to_float wrong label:" ^ s)
    | Tuple _ -> invalid_arg "arbogen_to_float, expected float but was tuple"

  let count_collect =
    let sum = List.fold_left Int.add in
    fold
      ~label:(fun lab -> sum (if String.equal lab "@collect" then 1 else 0))
      ~tuple:(sum 0)

  let generate grammar name rs =
    let search_seed grammar =
      let size_min = int_of_float (0.9 *. float !size) in
      let size_max = !size in
      let s =
        Boltzmann.search_seed
          (module Randtools.OcamlRandom)
          grammar ~size_min ~size_max
      in
      match s with
      | Some (_size, state) -> state
      | None ->
          Format.ksprintf failwith
            "Could not find a tree if size in [%d,\n      %d] in %d attempts"
            size_min size_max !max_try
    in
    Random.set_state rs ;
    let state = search_seed grammar in
    Randtools.OcamlRandom.set_state state ;
    fst @@ Boltzmann.free_gen (module Randtools.OcamlRandom) grammar name
end

(* collectors *)
module Collect = struct
  let unit _ () = [()]

  let bool _ (x : bool) = [x]

  let char _ (x : char) = [x]

  let int _ (x : int) = [x]

  let float _ (x : float) = [x]
end

let count = ref 1000

let reject pred g = QCheck.find_example ~f:pred ~count:!count g

let simplex seed (x : instance) (vectors : instance list) (nb_dim : int) =
  (* point obtained by translation of f1 by r*f1f2, r in [0;1]. FIXME: uniform
     for reals but not for floats *)
  let barycenter_f r f1 f2 = ((1. -. r) *. f1) +. (r *. f2) in
  (* same as barycenter_f using integers *)
  let barycenter_i r i1 i2 =
    ((1. -. r) *. float i1) +. (r *. float i2) |> int_of_float
  in
  (* Polyhedra primitives *)
  let f_vec r i1 i2 =
    List.map2
      (fun (v1, i1) (_, i2) ->
        match (i1, i2) with
        | GInt i1, GInt i2 -> (v1, GInt (barycenter_i r i1 i2))
        | GFloat f1, GFloat f2 -> (v1, GFloat (barycenter_f r f1 f2))
        | _ ->
            Format.asprintf "Type mismatch for variable %s" v1 |> invalid_arg
        )
      i1 i2
  in
  (* translation of i1 by r1*i1v1, r2*i1v2 ... rn*i1vn where r1 .. rn are
     random coeff in [0;1] *)
  let translate g1 (r : float list) vecs =
    List.fold_left2 (fun p r v -> f_vec r p v) g1 r vecs
  in
  let sum = ref 0. in
  let random_vecs =
    List.rev_map
      (fun _ ->
        let r = QCheck.Gen.float_bound_inclusive 1. seed in
        sum := !sum +. r ;
        r )
      vectors
  in
  translate x
    ( if !sum > (nb_dim |> float) /. 2. then
      List.rev_map (fun f -> 1. -. f) random_vecs
    else List.rev random_vecs )
    vectors

let increasing l =
  match l with
  | h :: t -> (
    try
      List.fold_left (fun acc e -> if acc <= e then e else raise Exit) h t
      |> ignore ;
      true
    with Exit -> false )
  | [] -> true

let increasing_strict l =
  match l with
  | h :: t -> (
    try
      List.fold_left (fun acc e -> if acc < e then e else raise Exit) h t
      |> ignore ;
      true
    with Exit -> false )
  | [] -> true

let decreasing l = List.rev l |> increasing

let decreasing_strict l = List.rev l |> increasing_strict

let alldiff l =
  let tbl = Hashtbl.create 1000 in
  try
    List.iter
      (fun e ->
        match Hashtbl.find_opt tbl e with
        | None -> Hashtbl.add tbl e () ; ()
        | Some _ -> raise Exit )
      l ;
    true
  with Exit -> false

let memo f =
  let tbl = Hashtbl.create 1000 in
  fun arg ->
    match Hashtbl.find_opt tbl arg with
    | None ->
        let value = f arg in
        Hashtbl.add tbl arg value ; value
    | Some value -> value

(* Redefinition of some operators to explicit types in constraints *)

module Operators = struct
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
end
