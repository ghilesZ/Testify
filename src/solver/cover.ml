module Make (D : Signatures.Abs) = struct
  (* TODO: define a more serious volume *)
  type vol = float

  type t =
    { inner: (D.t * vol) list (* sorted, increasing, volume-wise*)
    ; outer: (D.t * vol * Lang.constr) list
          (* sorted, decreasing, volume-wise*)
    ; inner_volume: vol
    ; total_volume: vol }

  let print fmt {inner; outer; _} =
    let print_list f =
      Format.pp_print_list ~pp_sep:(fun fmt _ -> Format.fprintf fmt "\n") f
    in
    Format.fprintf fmt "inner: %a\nouter: %a\n"
      (print_list (fun fmt (d, _) -> Format.fprintf fmt "%a" D.print d))
      inner
      (print_list (fun fmt (d, _, _) -> Format.fprintf fmt "%a" D.print d))
      outer

  let empty = {inner= []; outer= []; inner_volume= 0.; total_volume= 0.}

  (* true if the cover is a partition, ie the problem is solved *)
  let is_partition {outer; _} = outer = []

  (* gets the first (biggest) element of the outer elements *)
  let pop_outer cover =
    match cover.outer with
    | [] -> invalid_arg "no outer element"
    | ((_, vol, _) as h) :: tl ->
        (h, {cover with total_volume= cover.total_volume -. vol; outer= tl})

  let add_inner cover elm =
    let v = D.volume elm in
    { cover with
      inner= (elm, v) :: cover.inner
    ; inner_volume= cover.inner_volume +. v
    ; total_volume= cover.total_volume +. v }

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
    ; total_volume= cover.total_volume +. v }

  let ratio {inner_volume; total_volume; _} =
    let ratio = inner_volume /. total_volume in
    Format.printf "%f/%f = %f\n%!" inner_volume total_volume ratio ;
    ratio

  let compile cover =
    let inner_gens = List.map (fun (g, w) -> (w, D.compile g)) cover.inner in
    let outer_gens =
      List.map
        (fun (g, w, r) -> (w, Lang.to_ocaml r, D.compile g))
        cover.outer
    in
    (inner_gens, outer_gens)

  let threshold = ref 0.9

  let solve abs constr : t =
    let open Consistency in
    let rec aux cover =
      if ratio cover > !threshold || is_partition cover then cover
      else
        let (biggest, _, constr), cover' = pop_outer cover in
        if Lang.is_rejection constr then cover
        else
          let new_cover =
            match D.filter biggest constr with
            | Unsat -> cover
            | Sat -> add_inner cover' abs
            | Filtered ((abs', _), true) -> add_inner cover' abs'
            | Filtered ((abs', c), false) ->
                List.fold_left
                  (fun acc elm -> add_outer acc elm c)
                  cover (D.split abs')
          in
          aux new_cover
    in
    aux (add_outer empty abs constr)

  let get_generators i_s f_s constr =
    let abs = D.init i_s f_s in
    solve abs constr |> compile
end

module BoxCover = Make (Boolean.Make (Box))
