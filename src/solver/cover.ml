module Make (D : Signatures.Abs) = struct
  (* TODO: define a more serious volume *)
  type vol = float

  type t =
    { inner: (D.t * vol) list (* sorted, increasing, volume-wise*)
    ; outer: (D.t * vol * Lang.constr) list
          (* sorted, decreasing, volume-wise*)
    ; inner_volume: vol
    ; total_volume: vol }

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

  let compile compile_f cover =
    let inner_gens = List.map (fun (g, w) -> (w, compile_f g)) cover.inner in
    let outer_gens =
      List.map
        (fun (g, w, r) -> (w, Lang.to_ocaml r, compile_f g))
        cover.outer
    in
    (inner_gens, outer_gens)
end
