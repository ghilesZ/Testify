module Make (D : Signatures.Abs) = struct
  (* TODO: define a more serious volume *)
  type vol = float

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
    {inner= []; outer= []; inner_volume= 0.; total_volume= 0.; nb_elem= 0}

  (* true if the cover is a partition, ie the problem is solved *)
  let is_partition {outer; _} = outer = []

  (* gets the first (biggest) element of the outer elements *)
  let pop_outer c =
    match c.outer with
    | [] -> invalid_arg "no outer element"
    | ((_, vol, _) as h) :: tl ->
        ( h
        , { c with
            total_volume= c.total_volume -. vol
          ; outer= tl
          ; nb_elem= c.nb_elem - 1 } )

  let add_inner c elm =
    let v = D.volume elm in
    { c with
      inner= (elm, v) :: c.inner
    ; inner_volume= c.inner_volume +. v
    ; total_volume= c.total_volume +. v
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
    ; total_volume= cover.total_volume +. v
    ; nb_elem= cover.nb_elem + 1 }

  let ratio {inner_volume; total_volume; _} = inner_volume /. total_volume

  let satisfies _instance _constr = false

  let accept_rate _abs _constr =
    (* let rec aux nb nb_in =
     *   if nb <= 1000 then
     *     aux (nb + 1)
     *       (if satisfies (D.spawn abs) constr then nb_in + 1 else nb_in)
     *   else float nb_in /. float nb
     * in
     * aux 0 0 *)
    1.

  let compile cover =
    let inner_gens =
      List.rev_map (fun (abs, weight) -> (weight, D.compile abs)) cover.inner
    in
    let outer_gens =
      List.map
        (fun (abs, weight, constr) ->
          ( weight *. accept_rate abs constr
          , Lang.to_ocaml constr
          , D.compile abs ))
        cover.outer
    in
    (inner_gens, outer_gens)

  (* TODO: add option to change this *)
  let threshold = ref 0.999

  let max_size = ref 10

  let solve abs constr : t =
    let rec aux cover =
      if
        ratio cover > !threshold
        || is_partition cover || cover.nb_elem > !max_size
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
    let render = Rendering.create ~abciss:x ~ordinate:y 600. 600. in
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
    |> in_gtk_canvas

  let get_generators i_s f_s constr =
    let abs = D.init i_s f_s in
    let c = solve abs constr in
    (* show c (Tools.SSet.max_elt i_s) (Tools.SSet.min_elt i_s) ; *)
    compile c
end

module BoxCover = Make (Boolean.Make (Boxes))
module PolyCover = Make (Boolean.Make (Polyhedra))
