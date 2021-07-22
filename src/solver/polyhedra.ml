open Tools
open Apron
open Apronext
open Helper
open Generator1

type t = Apol.t

let join = Apol.join

let print fmt pol =
  let l = Apol.to_generator_list pol in
  Format.pp_print_list
    ~pp_sep:(fun fmt () -> Format.fprintf fmt ";\n")
    Generatorext.print fmt l

let manager = Polka.manager_alloc_strict ()

(* given a set of integer variables and a set of float variables, builds the
   unconstrained polyhedron defined on the given dimensions. Integers are
   bounded between Stdlib.min_int and Stdlib.max_int. Floats are bounded
   between Stdlib.-max_float Stdlib.max_float *)
let init =
  let i = Interval.of_int min_int max_int in
  let f = Interval.of_float min_float max_float in
  fun ints reals ->
    let i_arr = SSet.to_seq ints |> Array.of_seq in
    let r_arr = SSet.to_seq reals |> Array.of_seq in
    let ivars = Array.map Var.of_string i_arr in
    let rvars = Array.map Var.of_string r_arr in
    let env = Environment.make ivars rvars in
    let itvi = Array.map (fun _ -> i) i_arr in
    let itvr = Array.map (fun _ -> f) r_arr in
    let itvs = Array.concat [itvi; itvr] in
    let vars = Array.concat [ivars; rvars] in
    Abstract1.of_box manager env vars itvs

(* Conversion to apron constraint language *)
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
    | ToInt a -> Texprext.cast ~typ:Int (numeric a)
    | ToFloat a -> Texprext.cast ~typ:Real (numeric a)
  in
  fun a1 op a2 -> (cmp op) (numeric a1) (numeric a2)

(* filtering operation *)
let filter pol e1 cmp e2 =
  let tc = constraint_to_apron Abstract1.(pol.env) e1 cmp e2 in
  (* Format.printf "filtering %a\n%!" Tconsext.print tc ; *)
  let pol' = Apol.filter_tcons pol tc in
  if Apol.is_bottom pol' then Consistency.Unsat
  else
    let succ = Apol.is_bottom (Apol.filter_tcons pol' (Tconsext.neg tc)) in
    Consistency.Filtered (pol', succ)

(* extracts the variable with the largest interval range *)
let largest pol : Var.t * Interval.t =
  let env = pol.Abstract1.env in
  let box = Abstract1.to_box Apol.man pol in
  let itvs = box.Abstract1.interval_array in
  let len = Array.length itvs in
  let rec aux cur i_max diam_max itv_max =
    if cur >= len then (i_max, itv_max)
    else
      let e = itvs.(cur) in
      let diam = Intervalext.range_mpqf e in
      if Mpqf.cmp diam diam_max > 0 then aux (cur + 1) cur diam e
      else aux (cur + 1) i_max diam_max itv_max
  in
  let a, b = aux 0 0 (Mpqf.of_int 0) itvs.(0) in
  (Environment.var_of_dim env a, b)

(* split variable with largest dimension *)
let split pol =
  let env = Abstract1.env pol in
  let var, itv = largest pol in
  let mid = Intervalext.mid itv in
  let i1 = Coeff.i_of_scalar itv.inf mid in
  let i2 = Coeff.i_of_scalar mid itv.sup in
  let p1 = Apol.assign_texpr pol var (Texprext.cst env i1) in
  let p2 = Apol.assign_texpr pol var (Texprext.cst env i2) in
  [p1; p2]

(* difference operator *)
let diff p1 p2 = snd (Apol.set_diff p1 p2)

let split pol =
  (* Format.printf "entering split\n%!" ; *)
  let env = Abstract1.env pol in
  let nb_dim = Environmentext.size env in
  let gens = Apol.to_generator_list pol in
  let nb_gen = List.length gens in
  if nb_gen <= nb_dim + 1 then (* simplex -> regular split *) split pol
  else
    let p' = Apol.of_generator_list (n_first gens (nb_dim + 1)) in
    p' :: diff pol p'

let nb_gen p = p |> Apol.to_generator_list |> List.length

let nb_dim p = p |> Abstract1.env |> Environment.size

let is_simplex pol = nb_dim pol >= nb_gen pol - 1

let coeff_add c1 c2 =
  let open Coeff in
  match (c1, c2) with
  | Scalar s1, Scalar s2 -> Scalar (Scalarext.add s1 s2)
  | _ -> invalid_arg "non scalar coeff for generators"

let coeff_mul c1 c2 =
  let open Coeff in
  match (c1, c2) with
  | Scalar s1, Scalar s2 -> Scalar (Scalarext.mul s1 s2)
  | _ -> invalid_arg "non scalar coeff for generators"

let coeff_div c d =
  let open Coeff in
  match c with
  | Scalar s -> Scalar (Scalarext.div s (Scalar.of_int d))
  | _ -> invalid_arg "non scalar coeff for generators"

let compile_coeff typvar c =
  let open Environment in
  let open Coeff in
  match (typvar, c) with
  | REAL, Scalar s ->
      apply_nolbl_s "mk_float" [Scalarext.to_float s |> float_]
  | INT, Scalar s ->
      apply_nolbl_s "mk_int" [Scalarext.to_float s |> int_of_float |> int_]
  | _ -> invalid_arg "non scalar coeff"

let gen_to_instance g =
  let expr = ref empty_list_exp in
  let cons c v =
    let typ = Environment.typ_of_var g.env v in
    let var = pair (string_ (Var.to_string v)) (compile_coeff typ c) in
    expr := cons_exp var !expr
  in
  iter cons g ; !expr

let compile_simplex pol =
  match Apol.to_generator_list pol with
  | h :: tl ->
      let others = list_of_list (List.map gen_to_instance tl) in
      apply_nolbl_s "simplex" [gen_to_instance h; others; int_ (nb_dim pol)]
  | [] -> assert false

let barycenter = function
  | [] -> assert false
  | h :: tl ->
      let add_gen g1 g2 =
        let res = copy g1 in
        iter
          (fun c1 v ->
            let c2 = get_coeff g2 v in
            set_coeff res v (coeff_add c1 c2))
          g1 ;
        res
      in
      let g, nb =
        List.fold_left (fun (g, nb) g' -> (add_gen g g', nb + 1)) (h, 1) tl
      in
      let res = copy g in
      iter (fun c v -> set_coeff res v (coeff_div c nb)) g ;
      res

let dist g1 g2 =
  let res = ref (Coeffext.s_of_int 0) in
  iter
    (fun c1 v ->
      let c2 = get_coeff g2 v in
      let diff = coeff_add (Coeffext.neg c1) c2 in
      res := coeff_add !res (coeff_mul diff diff))
    g1 ;
  !res |> Coeffext.to_mpqf |> Mpqf.to_string |> Q.of_string |> Q.to_bigint

let vol_simplex pol =
  let rec loop dim acc = function
    | [] -> assert false
    | [_] -> acc
    | [g1; g2] -> Z.mul acc (dist g1 g2)
    | h :: tl ->
        Z.div
          (loop (dim - 1) (Z.mul acc (dist h (barycenter tl))) tl)
          (Z.of_int dim)
  in
  let l = Apol.to_generator_list pol in
  loop (List.length l - 1) Z.one l

let default_volume abs =
  let b = Abstract1.to_box Apol.man abs in
  b.Abstract1.interval_array
  |> Array.fold_left
       (fun v i ->
         let r = Intervalext.range i |> Scalarext.to_float |> int_of_float in
         if r = 0 then v else v * r)
       1
  |> Z.of_int

let volume pol =
  (* if is_simplex pol then vol_simplex pol else *) default_volume pol

open Migrate_parsetree
open Ast_410

let compile pol =
  let rec aux acc pol =
    if is_simplex pol then (volume pol, pol) :: acc
    else
      let p' = split pol in
      List.fold_left aux acc p'
  in
  if is_simplex pol then compile_simplex pol
  else
    let simplices = aux [] pol in
    let total =
      List.fold_left (fun acc (x, _) -> Z.add acc x) Z.zero simplices
    in
    let open Ast_helper in
    let gens =
      List.fold_left
        (fun acc (w, p) ->
          cons_exp
            (Exp.tuple
               [float_dec (Q.make w total |> Q.to_float); compile_simplex p])
            acc)
        empty_list_exp simplices
    in
    apply_nolbl_s "weighted" [gens]

(* Format.asprintf
 *   "can not compile not simplex polyhedra. Number of gens: %i\n@.[%a@]\n"
 *   (nb_gen pol) print pol
 * |> failwith *)

let to_drawable = Picasso.Drawable.of_pol
