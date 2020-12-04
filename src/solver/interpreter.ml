open Migrate_parsetree
open Ast_410
open Tools

module type Abs = sig
  type t

  val init : SSet.t -> SSet.t -> t

  val compile : t -> Parsetree.expression

  val split : t -> t list

  val filter : t -> Lang.constr -> (t * Lang.constr) Consistency.t

  val volume : t -> float
end

module Make (D : Abs) = struct
  type t = D.t * Lang.constr

  (* TODO: put option to change this *)
  let max_depth = ref 8

  (* returns a list of inner element and a list of pairs of outter elements
     and constraints *)
  let build_cover abs constr : D.t Cover.t =
    let open Consistency in
    let rec aux depth cover =
      if depth >= !max_depth then cover
      else
        try
          let (biggest, _, constr), cover' = Cover.pop_outer cover in
          if Lang.is_rejection constr then cover
          else
            let new_cover =
              match D.filter biggest constr with
              | Unsat -> cover
              | Sat -> Cover.add_inner cover' abs (D.volume abs)
              | Filtered ((abs', _), true) ->
                  Cover.add_inner cover' abs' (D.volume abs)
              | Filtered ((abs', c), false) ->
                  List.fold_left
                    (fun acc elm -> Cover.add_outer acc elm (D.volume elm) c)
                    cover (D.split abs')
            in
            aux (depth + 1) new_cover
        with Cover.NoOuter -> cover
    in
    aux 1 Cover.(add_outer empty abs (D.volume abs) constr)

  let compile cover =
    let open Cover in
    let inner_gens = List.map (fun (g, w) -> (w, D.compile g)) cover.inner in
    let outer_gens =
      List.map
        (fun (g, w, r) -> (w, Lang.to_ocaml r, D.compile g))
        cover.outer
    in
    (inner_gens, outer_gens)

  let get_generators i_s f_s constr =
    let abs = D.init i_s f_s in
    build_cover abs constr |> compile
end

module BoxInter = Make (Boolean.Make (Box))
