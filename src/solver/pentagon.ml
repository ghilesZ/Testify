module Num = struct
  type t = float

  let min_num = -.max_float

  let max_num = max_float
end

module Var = String
module VMap = Map.Make (Var)
module VSet = Set.Make (Var)

type t =
  { bounds: (Num.t * Num.t) VMap.t
  ; (* intervals where variables live *)
    upper: VSet.t VMap.t
  ; (* upper sets of each variable *)
    lower: VSet.t VMap.t
  ; (* lower sets of each variable *)
    vars: VSet.t
  ; (* list of variables *)
    reduced: bool (* transitively reduced or not *) }

let empty : t =
  { bounds= VMap.empty
  ; upper= VMap.empty
  ; lower= VMap.empty
  ; vars= VSet.empty
  ; reduced= true }

let add_var (var : Var.t) ?(inf = Num.min_num) ?(sup = Num.max_num)
    (pentagon : t) : t =
  assert (inf <= sup) ;
  { pentagon with
    bounds= VMap.add var (inf, sup) pentagon.bounds
  ; upper= VMap.add var VSet.empty pentagon.upper
  ; lower= VMap.add var VSet.empty pentagon.lower
  ; vars= VSet.add var pentagon.vars }

let rec paths pentagon (u : Var.t) (v : Var.t) : Var.t list list =
  if u = v then [[v]]
  else
    VSet.fold
      (fun u' acc -> List.map (fun l -> u :: l) (paths pentagon u' v) @ acc)
      (VMap.find u pentagon.upper)
      []

let del_rel v1 v2 pentagon : t =
  let updater y = function
    | None -> None
    | Some s -> Some ((VSet.remove y) s)
  in
  { pentagon with
    upper= VMap.update v1 (updater v2) pentagon.upper
  ; lower= VMap.update v2 (updater v1) pentagon.lower }

(* add relation v1 <= v2 *)
let add_rel (v1 : Var.t) (v2 : Var.t) (pentagon : t) : t =
  let updater y = function
    | None -> Some (VSet.singleton y)
    | Some s -> Some (VSet.add y s)
  in
  { pentagon with
    upper= VMap.update v1 (updater v2) pentagon.upper
  ; lower= VMap.update v2 (updater v1) pentagon.lower
  ; reduced= false }

let del_var v pentagon : t =
  let v_uppers = VMap.find v pentagon.upper in
  let v_lowers = VMap.find v pentagon.lower in
  { pentagon with
    upper= VMap.remove v pentagon.upper
  ; lower= VMap.remove v pentagon.lower
  ; bounds= VMap.remove v pentagon.bounds
  ; vars= VSet.remove v pentagon.vars }
  |> VSet.fold (del_rel v) v_uppers
  |> VSet.fold (fun x acc -> del_rel x v acc) v_lowers
  |> VSet.fold
       (fun u p ->
         VSet.fold
           (fun l p -> if paths p l u = [] then add_rel l u p else p)
           (* keep transitivity reduction *)
           v_lowers p)
       v_uppers

let sinks pentagon : VSet.t =
  VSet.filter
    (fun x -> VSet.equal VSet.empty (VMap.find x pentagon.upper))
    pentagon.vars

let sources pentagon : VSet.t =
  VSet.filter
    (fun x -> VSet.equal VSet.empty (VMap.find x pentagon.lower))
    pentagon.vars

let to_dot_file pentagon (filename : string) : unit =
  let buf = Buffer.create 1024 in
  Buffer.add_string buf "digraph G {\n" ;
  let label v =
    let inf, sup = VMap.find v pentagon.bounds in
    Printf.sprintf "%s [label=\"%s in [%.3e, %.3e]\"];\n" v v inf sup
  in
  VSet.iter (fun v -> Buffer.add_string buf (label v)) pentagon.vars ;
  VMap.iter
    (fun u vs ->
      VSet.iter (fun v -> Buffer.add_string buf (u ^ " -> " ^ v ^ ";\n")) vs)
    pentagon.upper ;
  Buffer.add_string buf "}\n" ;
  let fd = Stdlib.open_out filename in
  (* print_endline (Buffer.contents buf); *)
  Buffer.output_buffer fd buf ;
  close_out fd

let str_of_pentagon p =
  String.concat "\n"
    (List.concat_map
       (fun v ->
         VSet.elements
         @@ VSet.map
              (fun u -> Printf.sprintf "%s < %s" v u)
              (VMap.find v p.upper))
       (VSet.elements p.vars))
  ^ "\n"
  ^ String.concat "\n"
      ( VSet.elements
      @@ VSet.map
           (fun v ->
             let lo, up = VMap.find v p.bounds in
             Printf.sprintf "%s [%.3e, %.3e]" v lo up)
           p.vars )

let show pentagon =
  let temp_file = "temp_dot_" ^ string_of_float (Sys.time ()) in
  to_dot_file pentagon temp_file ;
  ignore @@ Sys.command ("dot -Tpdf -O " ^ temp_file) ;
  ignore @@ Sys.command ("xdg-open " ^ temp_file ^ ".pdf")

(* Sys.remove temp_file;
 * Sys.remove (temp_file ^ ".pdf") *)

let transitive_reduction (pentagon : t) : t =
  let sinks = sinks pentagon in
  let rec reduce_srcs_floors pentagon srcs =
    (* fold of the levels of the DAG *)
    if VSet.for_all (fun src -> VSet.mem src sinks) srcs then pentagon
    else
      let first_floor_reduced =
        VSet.fold
          (fun src pentagon ->
            VSet.fold
              (fun src' pentagon ->
                let pentagon' = del_rel src src' pentagon in
                match paths pentagon' src src' with
                | [] -> pentagon
                | _ -> pentagon')
              (VMap.find src pentagon.upper)
              pentagon)
          srcs pentagon
      in
      let next_floor =
        VSet.fold
          (fun src nexts ->
            VSet.union nexts (VMap.find src first_floor_reduced.upper))
          srcs VSet.empty
      in
      reduce_srcs_floors first_floor_reduced next_floor
  in
  if pentagon.reduced then pentagon
  else {(reduce_srcs_floors pentagon (sources pentagon)) with reduced= true}

let find_var p =
  VSet.find_first_opt
    (fun v ->
      let uc = VSet.cardinal (VMap.find v p.upper) in
      let ul = VSet.cardinal (VMap.find v p.lower) in
      uc <= 1 && ul <= 1)
    p.vars

let find_vars p =
  let rec find_vars (s1 : VSet.t) (s2 : VSet.t) =
    let x = VSet.choose s1 in
    let y = VSet.find_first_opt (fun y -> paths p x y = []) s2 in
    match y with None -> find_vars (VSet.remove x s1) s2 | Some y -> (x, y)
  in
  find_vars p.vars p.vars

type rule = B of Var.t | I of Var.t | T of Var.t | E of Var.t

let str_of_rule = function
  | E v -> Printf.sprintf "E %s" v
  | B v -> Printf.sprintf "B %s" v
  | I v -> Printf.sprintf "I %s" v
  | T v -> Printf.sprintf "T %s" v

let unfold_bit_decomp pentagon =
  let rec fold acc todo =
    match todo with
    | [] -> acc
    | (ord, orig, p) :: q -> (
        if VSet.equal p.vars VSet.empty then
          fold ((List.rev ord, orig) :: acc) q
        else
          match find_var p with
          | None ->
              let x, y = find_vars p in
              let f p = transitive_reduction @@ add_rel x y p in
              let g p = transitive_reduction @@ add_rel y x p in
              fold acc ((ord, f orig, f p) :: (ord, g orig, g p) :: q)
          | Some v ->
              let uc = VSet.cardinal (VMap.find v p.upper) in
              let ul = VSet.cardinal (VMap.find v p.lower) in
              (* Printf.printf "%s %d %d\n" v uc ul; *)
              print_endline (str_of_pentagon p) ;
              let v' =
                match (uc, ul) with
                | 0, 0 -> E v
                | 0, 1 -> B v
                | 1, 0 -> T v
                | 1, 1 -> I v
                | _ -> assert false
              in
              fold acc ((v' :: ord, orig, del_var v p) :: q) )
  in
  let p = transitive_reduction pentagon in
  fold [] [([], p, p)]

let rec str_of_bit_decomp (decomp, p) =
  match decomp with
  | [] -> "\n" ^ str_of_pentagon p
  | r :: q -> str_of_rule r ^ " " ^ str_of_bit_decomp (q, p)

type scalar = V of Var.t | N of Num.t

let unfold_bounds_const ord pentagon =
  let rec b_handler acc ord p u v =
    let vlo, vup = VMap.find v p.bounds in
    let ulo, uup = VMap.find u p.bounds in
    match (uup < vlo, ulo < vlo) with
    | true, _ ->
        fold
          (List.map (fun x -> (v, N vlo, N vup) :: x) acc)
          ord (del_var v p)
    | false, true ->
        fold
          (List.map (fun x -> (v, V u, N vup) :: x) acc)
          ord
          (del_var v {p with bounds= VMap.add u (vlo, min vup uup) p.bounds})
        @ fold
            (List.map (fun x -> (v, N vlo, N vup) :: x) acc)
            ord
            (del_var v {p with bounds= VMap.add u (ulo, vlo) p.bounds})
    | _ ->
        fold
          (List.map (fun x -> (v, V u, N vup) :: x) acc)
          ord
          (del_var v {p with bounds= VMap.add u (ulo, min vup uup) p.bounds})
  and t_handler acc ord p u v =
    let vlo, vup = VMap.find v p.bounds in
    let ulo, uup = VMap.find u p.bounds in
    match (vup < ulo, uup > vup) with
    | true, _ ->
        fold
          (List.map (fun x -> (v, N vlo, N vup) :: x) acc)
          ord (del_var v p)
    | false, true ->
        fold
          (List.map (fun x -> (v, N vlo, N vup) :: x) acc)
          ord
          (del_var v {p with bounds= VMap.add u (vup, uup) p.bounds})
        @ fold
            (List.map (fun x -> (v, N vlo, V u) :: x) acc)
            ord
            (del_var v
               {p with bounds= VMap.add u (max vlo ulo, vup) p.bounds})
    | _ ->
        fold
          (List.map (fun x -> (v, N vlo, V u) :: x) acc)
          ord
          (del_var v {p with bounds= VMap.add u (max vlo ulo, uup) p.bounds})
  and fold acc ord p =
    match ord with
    | [] -> List.map List.rev acc
    | r :: ord' -> (
      match r with
      | B v ->
          (* case v > u *)
          let u = VSet.choose @@ VMap.find v p.lower in
          b_handler acc ord' p u v
      | T v ->
          (* case v < u *)
          let u = VSet.choose @@ VMap.find v p.upper in
          t_handler acc ord' p u v
      | E v ->
          let vlo, vup = VMap.find v p.bounds in
          fold (List.map (fun x -> (v, N vlo, N vup) :: x) acc) ord' empty
      | I v -> (
          (* case u < v < w *)
          let u = VSet.choose @@ VMap.find v p.lower in
          let w = VSet.choose @@ VMap.find v p.upper in
          let vlo, vup = VMap.find v p.bounds in
          let ulo, uup = VMap.find u p.bounds in
          let wlo, wup = VMap.find w p.bounds in
          match (uup < vlo, vup < wlo) with
          | true, true ->
              fold
                (List.map (fun x -> (v, N vlo, N vup) :: x) acc)
                ord' (del_var v p)
          | true, false -> t_handler acc ord' p w v
          | false, true -> b_handler acc ord' p u v
          | false, false ->
              ( if ulo < vlo && vup < wup then
                fold
                  (List.map (fun x -> (v, N vlo, N vup) :: x) acc)
                  ord'
                  (del_var v
                     { p with
                       bounds=
                         p.bounds
                         |> VMap.add u (ulo, vlo)
                         |> VMap.add w (vup, wup) })
              else [] )
              @ fold
                  (List.map (fun x -> (v, V u, V w) :: x) acc)
                  ord'
                  (del_var v
                     { p with
                       bounds=
                         p.bounds
                         |> VMap.add u (ulo, min vup uup)
                         |> VMap.add w (max vlo wlo, wup) }) ) )
  in
  fold [[]] ord pentagon

let str_of_scalar = function V v -> v | N v -> Printf.sprintf "%.3e" v

let latex_of_formula formula =
  let rec aux inner_formula = function
    | [] -> inner_formula
    | (v, lo, up) :: f ->
        let inner_formula =
          Printf.sprintf "\\int_{%s}^{%s} %s \\mathrm{d} {%s}~"
            (str_of_scalar lo) (str_of_scalar up) inner_formula v
        in
        aux inner_formula f
  in
  aux "" formula

let p =
  empty
  |> add_var "x0" ~inf:1. ~sup:2.
  |> add_var "x1" ~inf:3. |> add_var "x2" |> add_var "x3"
  |> add_rel "x0" "x1" |> add_rel "x0" "x2" |> add_rel "x0" "x3"
  |> add_rel "x1" "x2" |> add_rel "x3" "x2" |> add_rel "x3" "x1"

let p' =
  List.fold_left (fun acc x -> add_var x acc) empty ["x0"; "x1"; "x2"; "x3"]
  |> add_rel "x0" "x2" |> add_rel "x0" "x3" |> add_rel "x1" "x2"
  |> add_rel "x1" "x3"

let p_simple =
  empty
  |> add_var "x0" ~inf:0. ~sup:3.
  |> add_var "x1" ~inf:1. ~sup:4.
  |> add_var "x2" ~inf:2. ~sup:5.
  |> add_rel "x0" "x1" |> add_rel "x1" "x2"

(* let _ =
 *   (\* let p = p_simple in *\)
 *   (\* show (transitive_reduction p) ; *\)
 *   (\* let decomp = unfold_bit_decomp p in
 *    * List.iter (fun x -> print_endline @@ str_of_bit_decomp x) decomp ; *\)
 *   (\* print_endline (str_of_pentagon p_simple); *\)
 *   let decomp = [[I "x1"; T "x0"; E "x2"], p_simple] in
 *   Printf.printf "\\documentclass{article}\n\\begin{document}\n$$\\begin{array}{l}\n" ;
 *   List.iter
 *     (fun x -> print_endline ("\\displaystyle" ^ (latex_of_formula x) ^ "\\\\"))
 *     (List.concat_map (fun (ord, p) -> unfold_bounds_const ord p) decomp) ;
 *   Printf.printf "\\end{array}\n$$\n\\end{document}\n" *)

(* let _ =
 *   show p;
 *   show (del_rel "x0" "x2" p);
 *   show @@ transitive_reduction p
 *   (\\* Sys.command "rm temp_dot*" *\\) *)
