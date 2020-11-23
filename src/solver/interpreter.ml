open Migrate_parsetree
open Ast_410
open Helper
open Ast_helper
open Tools

module type Abs = sig
  type t

  val init : SSet.t -> SSet.t -> t

  val compile : t -> Parsetree.expression

  val split : t -> t list

  val filter : t -> Lang.constr -> t Consistency.t

  val volume : t -> float
end

(* TODO: define a more serious volume *)
type volume = float

type 'a cover =
  { inner: ('a * volume) list
  ; outer: ('a * volume * Parsetree.expression) list }

let empty = {inner= []; outer= []}

module Make (D : Abs) = struct
  type t = {space: D.t; constr: Lang.constr list}

  (* filtering constraints in turn only once *)
  let propagate {space; constr} : t Consistency.t =
    let open Consistency in
    let rec loop sat acc abs = function
      | [] -> Filtered ({space= abs; constr= acc}, sat)
      | c :: tl -> (
        match D.filter abs c with
        | Sat -> loop sat acc abs tl
        | Unsat -> Unsat
        | Filtered (abs', true) -> loop sat acc abs' tl
        | Filtered (abs', false) -> loop false (c :: acc) abs' tl )
    in
    loop true [] space constr

  let split elm = List.map (fun e -> {elm with space= e}) (D.split elm.space)

  let add_inner r x =
    let vx = D.volume x in
    {r with inner= (x, vx) :: r.inner}

  let add_outer r x rej =
    let vx = D.volume x in
    {r with outer= (x, vx, rej) :: r.outer}

  (* TODO: put option to change this *)
  let max_depth = ref 10

  (* compiles a non_empty list of constraint into an OCaml expression*)
  let to_expression = function
    | [] -> assert false
    | h :: t ->
        List.fold_left
          (fun acc e -> apply_nolbl_s "&&" [acc; Lang.to_ocaml e])
          (Lang.to_ocaml h) t

  (* returns a list of inner element and a list of pairs of outter elements
     and constraints *)
  let build_cover abs constr : D.t cover =
    let open Lang in
    let rec split_conjunction = function
      | Boolop (c1, And, c2) -> split_conjunction c1 @ split_conjunction c2
      | x -> [x]
    in
    let open Consistency in
    let rec aux depth res abs =
      match propagate abs with
      | Unsat -> res
      | Sat -> add_inner res abs.space
      | Filtered (abs', true) -> add_inner res abs'.space
      | Filtered (abs', false) ->
          if depth >= !max_depth then
            let reject = to_expression abs'.constr in
            add_outer res abs'.space reject
          else split abs' |> List.fold_left (aux (depth + 1)) res
    in
    aux 1 empty {space= abs; constr = split_conjunction constr}

  (* pattern is needed to recompile constraint into ocaml predicates *)
  let compile_cover {inner; outer} pattern : Parsetree.expression =
    let inner_gens =
      List.fold_left
        (fun acc (g, w) ->
          cons_exp (Exp.tuple [float_exp w; D.compile g]) acc)
        empty_list_exp inner
    in
    let outer_gens =
      List.fold_left
        (fun acc (g, w, reject) ->
          let g =
            apply_runtime "reject" [lambda pattern reject; D.compile g]
          in
          cons_exp (Exp.tuple [float_exp w; g]) acc)
        empty_list_exp outer
    in
    [apply_nolbl_s "@" [inner_gens; outer_gens]] |> apply_runtime "weighted"

end

module BoxInter = Make(Box)
