module Make (D : Signatures.Abs) = struct
  (* TODO: define a more serious volume *)
  type vol = Z.t

  type t =
    { inner: (D.t * vol) list (* sorted, increasing volume *)
    ; outer: (D.t * vol * Lang.constr) list (* sorted decreasing volume*)
    ; inner_volume: vol
    ; total_volume: vol
    ; nb_elem: int }

  let print fmt {inner; outer; _} =
    let print_list f =
      Format.pp_print_list ~pp_sep:(fun fmt _ -> Format.fprintf fmt "\n") f
    in
    Format.fprintf fmt "inner: %a\nouter: %a\n"
      (print_list (fun fmt (d, _) -> Format.fprintf fmt "%a" D.print d))
      inner
      (print_list (fun fmt (d, _, _) -> Format.fprintf fmt "%a" D.print d))
      outer

  let empty =
    { inner= []
    ; outer= []
    ; inner_volume= Z.zero
    ; total_volume= Z.zero
    ; nb_elem= 0 }

  (* true if the cover is a partition, ie the problem is solved *)
  let is_partition {outer; _} = outer = []

  (* gets the first (biggest) element of the outer elements *)
  let pop_outer c =
    match c.outer with
    | [] -> invalid_arg "no outer element"
    | ((_, vol, _) as h) :: tl ->
        ( h
        , { c with
            total_volume= Z.sub c.total_volume vol
          ; outer= tl
          ; nb_elem= c.nb_elem - 1 } )

  let add_inner c elm =
    let v = D.volume elm in
    { c with
      inner= (elm, v) :: c.inner
    ; inner_volume= Z.add c.inner_volume v
    ; total_volume= Z.add c.total_volume v
    ; nb_elem= c.nb_elem + 1 }

  (* insertion maintaining the order *)
  let add_outer cover elm (c : Lang.constr) =
    let v = D.volume elm in
    let rec add_outer ((_, vol, _) as x) = function
      | [] -> [x]
      | ((_, vol', _) as h) :: tl ->
          if vol > vol' then x :: h :: tl else h :: add_outer x tl
    in
    { cover with
      outer= add_outer (elm, v, c) cover.outer
    ; total_volume= Z.add cover.total_volume v
    ; nb_elem= cover.nb_elem + 1 }

  let ratio {inner_volume; total_volume; _} =
    Q.(div (of_bigint inner_volume) (of_bigint total_volume) |> to_float)

  let compile is fs cover =
    let inner_gens =
      List.rev_map (fun (abs, weight) -> (weight, D.compile abs)) cover.inner
    in
    let outer_gens =
      List.map
        (fun (abs, weight, constr) ->
          (weight, Lang.to_ocaml is fs constr, D.compile abs))
        cover.outer
    in
    (inner_gens, outer_gens)

  let threshold = ref 0.99

  let solve abs constr max : t =
    let rec aux cover =
      if
        ratio cover > !threshold || is_partition cover || cover.nb_elem > max
      then cover
      else
        let (biggest, _, constr), cover' = pop_outer cover in
        if Lang.is_rejection constr then cover
        else
          let new_cover =
            match D.filter biggest constr with
            | Unsat -> cover'
            | Sat -> add_inner cover' biggest
            | Filtered ((abs', _), true) -> add_inner cover' abs'
            | Filtered ((abs', c), false) ->
                List.fold_left
                  (fun acc elm -> add_outer acc elm c)
                  cover' (D.split abs')
          in
          aux new_cover
    in
    aux (add_outer empty abs constr)

  let show {inner; outer; _} x y =
    let open Picasso in
    let render =
      Rendering.create ~axis:false ~abciss:x ~ordinate:y 600. 600.
    in
    let render =
      List.fold_left Rendering.add render
        (List.map
           (fun (e, _) -> (Colors.rgb 200 200 255, D.to_drawable e))
           inner)
    in
    List.fold_left Rendering.add render
      (List.map
         (fun (e, _, _) -> (Colors.rgb 250 200 200, D.to_drawable e))
         outer)
    |> to_svg

  let get_generators i_s f_s constr max =
    let abs = D.init i_s f_s in
    let c = solve abs constr max in
    (*let min = try Tools.SSet.min_elt i_s with Not_found ->
      Tools.SSet.min_elt f_s in let max = try Tools.SSet.max_elt i_s with
      Not_found -> Tools.SSet.max_elt f_s in if !Log.log then show c max min
      "name" ; *)
    let inner, outer = compile i_s f_s c in
    (inner, outer, c.total_volume)
end

module Box = Make (Boolean.Make (Boxes))
module Pol = Make (Boolean.Make (Polyhedra))
