(* type pos = (int[@satisfying fun x -> x >= 0])
 *
 * let mean (pl : pos list) : pos option =
 *   let rec loop (sum, nb) = function
 *     | [] -> sum / nb
 *     | h :: tl -> loop (sum + h, nb + 1) tl
 *   in
 *   match pl with [] -> None | h :: tl -> Some (loop (h, 1) tl) *)
