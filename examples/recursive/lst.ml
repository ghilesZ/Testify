type pos = (int[@satisfying fun x -> x >= 0])

type 'a lst = 'a list = [] | ( :: ) of 'a * 'a list

(* let length (l : int lst) : pos = List.length l *)

type pos_list = Empty | Cons of pos * pos_list

type pair = pos_list * float

(* let mean (pl : pos_list) : pos =
 *   let rec loop (sum, nb) = function
 *     | Empty -> sum / nb
 *     | Cons (h, tl) -> loop (sum + h, nb + 1) tl
 *   in
 *   loop (0, 0) pl *)
