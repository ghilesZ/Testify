
module Num =
  struct
    type t = float
    let min_num = -. max_float
    let max_num = max_float
  end


module Var = String
module VMap = Map.Make(Var)
module VSet = Set.Make(Var)
  

type t = {bounds : (Num.t * Num.t) VMap.t; (* intervals where variables live *)
          upper : VSet.t VMap.t; (* upper sets of each variable *)
          lower : VSet.t VMap.t; (* lower sets of each variable *)
          vars : VSet.t; (* list of variables *)
          reduced : bool; (* transitively reduced or not *)
         } 

let empty : t = {bounds = VMap.empty;
                 upper = VMap.empty;
                 lower = VMap.empty;
                 vars = VSet.empty;
                 reduced = true}

let add_var (var : Var.t) ?(inf=Num.min_num) ?(sup=Num.max_num) (pentagon : t) : t =
  {pentagon with
    bounds = VMap.add var (inf,sup) pentagon.bounds;
    upper = VMap.add var VSet.empty pentagon.upper;
    lower = VMap.add var VSet.empty pentagon.lower;
    vars = VSet.add var pentagon.vars}

let rec paths pentagon (u:Var.t) (v:Var.t) : (Var.t list) list =
  if u = v then
    [[v]]
  else
    VSet.fold
      (fun u' acc -> (List.map (fun l -> u :: l) (paths pentagon u' v)) @ acc)
      (VMap.find u pentagon.upper)
      []

let del_rel v1 v2 pentagon : t =
  let updater y = function
      None -> None
    | Some s -> Some (VSet.remove y s) in
  {pentagon with
    upper = VMap.update v1 (updater v2) pentagon.upper;
    lower = VMap.update v2 (updater v1) pentagon.lower}

(* add relation v1 <= v2 *)
let add_rel (v1 : Var.t) (v2 : Var.t) (pentagon : t) : t =
  let updater y = (function
                     None -> Some (VSet.singleton y)
                   | Some s -> Some (VSet.add y s)) in
  {pentagon with
    upper = VMap.update v1 (updater v2) pentagon.upper;
    lower = VMap.update v2 (updater v1) pentagon.lower;
    reduced = false}                 

let del_var v pentagon : t =
  let v_uppers = VMap.find v pentagon.upper in
  let v_lowers = VMap.find v pentagon.lower in
  {pentagon with
    upper = VMap.remove v pentagon.upper;
    lower = VMap.remove v pentagon.lower;
    bounds = VMap.remove v pentagon.bounds;
    vars = VSet.remove v pentagon.vars}
  |> VSet.fold (del_rel v) v_uppers
  |> VSet.fold (fun x acc -> del_rel x v acc) v_lowers
  |> VSet.fold (fun u p ->
         VSet.fold (fun l p ->
             if paths p u l = [] then add_rel u l p else p) (* keep transitivity reduction *)
           v_lowers p)
       v_uppers
  
let sinks pentagon : VSet.t =
  VSet.filter (fun x -> VSet.equal VSet.empty (VMap.find x pentagon.upper)) pentagon.vars

let sources pentagon : VSet.t =
  VSet.filter (fun x -> VSet.equal VSet.empty (VMap.find x pentagon.lower)) pentagon.vars

let to_dot_file pentagon (filename:string) : unit =
  let buf = Buffer.create 1024 in
  Buffer.add_string buf "digraph G {\n";
  let label = (fun v ->
      let inf, sup = VMap.find v pentagon.bounds in
      Printf.sprintf "%s [label=\"%s in [%e, %e]\"];\n" v v inf sup)
  in
  VSet.iter (fun v -> Buffer.add_string buf (label v)) pentagon.vars;
  VMap.iter (fun u vs ->
      VSet.iter (fun v ->  Buffer.add_string buf (u ^ " -> " ^ v ^ ";\n")) vs)
    pentagon.upper;
  Buffer.add_string buf "}\n";
  let fd = Stdlib.open_out filename in
  (* print_endline (Buffer.contents buf); *)
  Buffer.output_buffer fd buf;
  close_out fd

let show pentagon =
  let temp_file = ("temp_dot_" ^ (string_of_float (Sys.time ()))) in
  to_dot_file pentagon temp_file;
  ignore @@ Sys.command ("dot -Tpdf -O " ^ temp_file);
  ignore @@ Sys.command ("xdg-open " ^ temp_file ^ ".pdf")
  (* Sys.remove temp_file;
   * Sys.remove (temp_file ^ ".pdf") *)

let transitive_reduction (pentagon:t) : t =
  let sinks = sinks pentagon in
  let rec reduce_srcs_floors pentagon srcs = (* fold of the levels of the DAG *)
    if VSet.for_all (fun src -> VSet.mem src sinks) srcs then
      pentagon
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
          srcs
          pentagon in
      let next_floor = VSet.fold
                         (fun src nexts ->
                           VSet.union nexts (VMap.find src first_floor_reduced.upper))
                         srcs
                         VSet.empty in
      reduce_srcs_floors first_floor_reduced next_floor in
  if pentagon.reduced then
    pentagon
  else
    {(reduce_srcs_floors pentagon (sources pentagon)) with
      reduced = true}

let find_var p =
  VSet.find_first_opt
    (fun v -> VSet.cardinal (VMap.find v p.upper) <= 1
              && VSet.cardinal (VMap.find v p.lower) <= 1)
    p.vars

let find_vars p =
  let rec find_vars (s1:VSet.t) (s2:VSet.t) =
    let x = VSet.choose s1 in
    let y =  VSet.find_first_opt (fun y -> paths p x y = []) s2 in
    match y with
    | None -> find_vars (VSet.remove x s1) s2
    | Some y -> x,y in
  find_vars p.vars p.vars

let unfold_bit_decomp pentagon =
  let rec fold acc todo =
    match todo with
      [] -> acc
    | (ord, orig, p) :: q ->
       if VSet.equal p.vars VSet.empty then
         fold ((ord,orig)::acc) q
       else
         (match find_var p with
         | None -> let x,y = find_vars p in
                   let f p = transitive_reduction @@ add_rel x y p in
                   let g p = transitive_reduction @@ add_rel y x p in
                   fold acc ((ord, f orig, f p)::(ord, g orig, g p)::q)
         | Some v -> fold acc (((v::ord), orig, del_var v p)::q)) in
  let p = transitive_reduction pentagon in
  fold [] [([],p,p)]
  
let p = empty
        |> add_var "x0" ~inf:1. ~sup:2.
        |> add_var "x1" ~inf:3.
        |> add_var "x2"
        |> add_var "x3"
        |> add_rel "x0" "x1"
        |> add_rel "x0" "x2"
        |> add_rel "x0" "x3"
        |> add_rel "x1" "x2"
        |> add_rel "x3" "x2"
        |> add_rel "x3" "x1"

let p' = (List.fold_left (fun acc x -> add_var x acc) empty ["x0"; "x1"; "x2"; "x3"])
         |> add_rel "x0" "x2"
         |> add_rel "x0" "x3"
         |> add_rel "x1" "x2"
         |> add_rel "x1" "x3"

let _ =
  unfold_bit_decomp p'

(* let _ =
 *   show p;
 *   show (del_rel "x0" "x2" p);
 *   show @@ transitive_reduction p
 *   (\* Sys.command "rm temp_dot*" *\) *)