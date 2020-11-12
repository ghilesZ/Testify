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

type 'a cover =
  { inner: ('a * volume) list
  ; outer: ('a * volume * Parsetree.expression) list }

(* TODO: define a more serious volume *)
and volume = float

module Make (D : Abs) = struct
  (* returns a list of inner element and a list of pairs of outter elements
     and constraints *)
  let build_cover _abs _constr : D.t cover = assert false

  let compile_cover {inner; outer} : Parsetree.expression =
    let inner_gens =
      List.fold_left
        (fun acc (g, w) ->
          cons_exp (Exp.tuple [float_exp w; D.compile g]) acc)
        empty_list_exp inner
    in
    let outer_gens =
      List.fold_left
        (fun acc (g, w, reject) ->
          let g = apply_runtime "reject" [reject; D.compile g] in
          cons_exp (Exp.tuple [float_exp w; g]) acc)
        empty_list_exp outer
    in
    [apply_nolbl_s "@" [inner_gens; outer_gens]] |> apply_runtime "weighted"
end
