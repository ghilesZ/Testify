open Tools
open Apron
open Apronext
include Apronext.Apol

let manager = Polka.manager_alloc_strict ()

(* given a set of integer variables and a set of float variables, builds the
   unconstrained polyhedron defined on the given dimensions. Integers are
   bounded between Stdlib.min_int and Stdlib.max_int. Floats are bounded
   between Stdlib.min_float Stdlib.max_float *)
let init =
  let i = Interval.of_int min_int max_int in
  let f = Interval.of_float min_float max_float in
  fun ints reals ->
    let i_arr = SSet.to_seq ints |> Array.of_seq in
    let r_arr = SSet.to_seq reals |> Array.of_seq in
    let ivars = Array.map Var.of_string i_arr in
    let rvars = Array.map Var.of_string r_arr in
    let env = Environment.make ivars rvars in
    let itvi = Array.make (Array.length i_arr) i in
    let itvr = Array.make (Array.length r_arr) f in
    let itvs = Array.concat [itvi; itvr] in
    let vars = Array.concat [ivars; rvars] in
    Abstract1.of_box manager env vars itvs

let constraint_to_apron env =
  let open Lang in
  let open Apronext in
  let cmp = function
    | Geq -> Tconsext.geq
    | Leq -> Tconsext.leq
    | Gt -> Tconsext.gt
    | Lt -> Tconsext.lt
    | Eq -> Tconsext.eq
    | Diseq -> Tconsext.diseq
  in
  let op = function
    | Add -> Texprext.add ~typ:Int
    | Sub -> Texprext.sub ~typ:Int
    | Mul -> Texprext.mul ~typ:Int
    | Div -> Texprext.div ~typ:Int
    | AddF -> Texprext.add ~typ:Real
    | SubF -> Texprext.sub ~typ:Real
    | MulF -> Texprext.mul ~typ:Real
    | DivF -> Texprext.div ~typ:Real
    | Pow -> Texprext.pow ~typ:Real
  in
  let rec numeric (d : arith) =
    match d with
    | Int x -> Texprext.cst env (Coeff.s_of_int x)
    | Float x -> Texprext.cst env (Coeff.s_of_float x)
    | Var v -> Texprext.var env (Var.of_string v)
    | Binop (a1, b, a2) -> (op b) (numeric a1) (numeric a2)
    | Neg a -> Texprext.neg ~typ:Int (numeric a)
    | NegF a -> Texprext.neg ~typ:Real (numeric a)
    | ToInt _a -> assert false
    | ToFloat _a -> assert false
  in
  let comparison a1 op a2 = (cmp op) (numeric a1) (numeric a2) in
  comparison

let filter pol e1 cmp e2 =
  let tc = constraint_to_apron Abstract1.(pol.env) e1 cmp e2 in
  let pol' = filter_tcons pol tc in
  if is_bottom pol' then Consistency.Unsat
  else
    let succ = is_bottom (filter_tcons pol (Tconsext.neg tc)) in
    Consistency.Filtered (pol, succ)

let split _ = failwith "poly.split"

let compile _ = failwith "poly.compile"

let volume _ = failwith "poly.volume"
