(* type sorted = int list [@@satisfying fun x -> sorted x] *)

(* let merge (s1 : sorted) (s2 : sorted) : sorted =
 *   let rec aux acc l r =
 *     match (l, r) with
 *     | [], [] -> List.rev acc
 *     | h :: tl, [] -> aux (h :: acc) tl []
 *     | [], _ -> aux acc r l
 *     | lhd :: ltl, rhd :: _ when lhd < rhd -> aux (lhd :: acc) ltl r
 *     | _ :: _, rhd :: rtl -> aux (rhd :: acc) l rtl
 *   in
 *   aux [] s1 s2 *)
