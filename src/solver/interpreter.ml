open Signatures

module Make (D : Abs) = struct
  module Cover = Cover.Make (D)

  type t = D.t * Lang.constr

  (* TODO: put option to change this *)
  let ratio = ref 0.1

  (* returns a list of inner element and a list of pairs of outter elements
     and constraints *)
  let build_cover abs constr : Cover.t =
    let open Consistency in
    let rec aux cover =
      if Cover.ratio cover > !ratio || Cover.is_partition cover then cover
      else
        let (biggest, _, constr), cover' = Cover.pop_outer cover in
        if Lang.is_rejection constr then cover
        else
          let new_cover =
            match D.filter biggest constr with
            | Unsat -> cover
            | Sat -> Cover.add_inner cover' abs
            | Filtered ((abs', _), true) -> Cover.add_inner cover' abs'
            | Filtered ((abs', c), false) ->
                List.fold_left
                  (fun acc elm -> Cover.add_outer acc elm c)
                  cover (D.split abs')
          in
          aux new_cover
    in
    aux Cover.(add_outer empty abs constr)

  let get_generators i_s f_s constr =
    let abs = D.init i_s f_s in
    build_cover abs constr |> Cover.compile D.compile
end

module BoxInter = Make (Boolean.Make (Box))
