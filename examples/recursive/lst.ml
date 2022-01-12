type sorted = Empty | Cons of int * sorted [@@satisfying fun x -> sorted x]

let rec sorted = function
  | x :: (y :: _ as tl) -> x <= y && sorted tl
  | _ -> true

let rev l =
  let rec aux acc = function
    | Empty -> acc
    | Cons (h, tl) -> aux (Cons (h, acc)) tl
  in
  aux Empty l

let merge (s1 : sorted) (s2 : sorted) : sorted =
  let rec aux acc l r =
    match (l, r) with
    | Empty, Empty -> rev acc
    | Cons (h, tl), Empty -> aux (Cons (h, acc)) tl Empty
    | Empty, _ -> aux acc r l
    | Cons (lhd, ltl), Cons (rhd, _) when lhd < rhd ->
        aux (Cons (lhd, acc)) ltl r
    | Cons (_, _), Cons (rhd, rtl) -> aux (Cons (rhd, acc)) l rtl
  in
  aux Empty s1 s2

(* (\* type of association lists where keys are sorted in increasing order and
 *    values in decreasing order *\)
 * type bi_sort =
 *   | Empty
 *   | Cons of ((int[@collect 1]) * (int[@collect 2])) * bi_sort
 * [@@satisfying
 *   fun x ->
 *     let l1, l2 = dfs x in
 *     increasing l1 && decreasing l2] *)

(* an other, shorter, possibility which uses DFS by default*)
type bi_sort =
  | Empty
  | Cons of ((int[@collect l1]) * (int[@collect l2])) * bi_sort
[@@satisfying increasing l1 && decreasing l2]
