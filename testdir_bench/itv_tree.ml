type interval_tree_x =
  | LeafX 
  | NodeX of ((int)[@collect 1]) * interval_tree_y * interval_tree_y *
  ((int)[@collect 2]) [@@satisfying
                        fun x -> (increasing x 1) && (increasing x 2)]
and interval_tree_y =
  | LeafY 
  | NodeY of (((int)[@collect 3]) * interval_tree_x * interval_tree_x *
  ((int)[@collect 4])) [@@satisfying
                         fun x -> (increasing x 3) && (increasing x 4)]

let gen_itv_tree rs =
  let rec of_arbogen_interval_tree_x arbg queue rs =
    match arbg with
    | Arbogen.Tree.Label
      ("interval_tree_x", (Tuple [])::child::[]) ->
       (match child with
        | Arbogen.Tree.Label ("LeafX", []) -> LeafX
        | Arbogen.Tree.Label ("NodeX", x1::x2::x3::x4::[]) ->
           let (x1, x2, x3, x4) =
             (fun queue ->
               fun rs ->
               let x1 =
                 Testify_runtime.Arbg.to_int x1 queue rs in
               let x2 =
                 of_arbogen_interval_tree_y x2 queue rs in
               let x3 =
                 of_arbogen_interval_tree_y x3 queue rs in
               let x4 =
                 Testify_runtime.Arbg.to_int x4 queue rs in
               (x1, x2, x3, x4)) queue rs in
           NodeX (x1, x2, x3, x4)
        | _ -> failwith "Ill-formed arbogen tree")
    | _ -> failwith "Ill-formed arbogen tree"
  and of_arbogen_interval_tree_y arbg queue rs =
    match arbg with
    | Arbogen.Tree.Label
      ("interval_tree_y", (Tuple [])::child::[]) ->
       (match child with
        | Arbogen.Tree.Label ("LeafY", []) -> LeafY
        | Arbogen.Tree.Label ("NodeY", x1::x2::x3::x4::[]) ->
           let x1' =
             (fun queue ->
               fun rs ->
               let x1 =
                 Testify_runtime.Arbg.to_int x1 queue rs in
               let x2 =
                 of_arbogen_interval_tree_x x2 queue rs in
               let x3 =
                 of_arbogen_interval_tree_x x3 queue rs in
               let x4 =
                 Testify_runtime.Arbg.to_int x4 queue rs in
               (x1, x2, x3, x4)) queue rs in
           NodeY x1'
        | _ -> failwith "Ill-formed arbogen tree")
    | _ -> failwith "Ill-formed arbogen tree" in
  let wg =
    let open Arbogen.Boltzmann.WeightedGrammar in
    {
      names =
        [|"interval_tree_x";"LeafX";"NodeX";"interval_tree_y";"LeafY";"NodeY";"@collect"|];
      rules =
        [|(Union
             [(0.500022361122, (Product [Z 1; Ref 1]));
              (0.499977638879, (Product [Z 1; Ref 2]))]);
          (Z 0);
          (Product [Ref 6; Ref 3; Ref 3; Ref 6]);
          (Union
              [(0.500022361122, (Product [Z 1; Ref 4]));
               (0.499977638879, (Product [Z 1; Ref 5]))]);
          (Z 0);
          (Product [Ref 6; Ref 0; Ref 0; Ref 6]);
          (Z 0)|]
    } in
  let tree =
    Testify_runtime.Arbg.generate wg "interval_tree_x" rs in
  let nb_collect = Testify_runtime.Arbg.count_collect tree in
  (* let queue = (fun n -> [|(Testify_runtime.Sicstus.increasing_list n)|]) nb_collect in *)
  let queue = [| List.init nb_collect (fun _ -> 0) |] in
  nb_collect, of_arbogen_interval_tree_x tree queue rs


let spec_itv_tree x =
  let rec collect_interval_tree_x n =
    function
    | LeafX -> []
    | NodeX (x1, x2, x3, x4) ->
       ((fun n ->
         fun (x1, x2, x3, x4) ->
         List.flatten
           [((fun n ->
              if n = 1
              then Testify_runtime.Collect.int n
              else (fun _ -> []))) n x1;
            collect_interval_tree_y n x2;
            collect_interval_tree_y n x3;
            ((fun n ->
              if n = 2
              then Testify_runtime.Collect.int n
              else (fun _ -> []))) n x4])) n (x1, x2, x3, x4)
  and collect_interval_tree_y n =
    function
    | LeafY -> []
    | NodeY x1 ->
       ((fun n ->
         fun (x1, x2, x3, x4) ->
         List.flatten
           [((fun n ->
              if n = 3
              then Testify_runtime.Collect.int n
              else (fun _ -> []))) n x1;
            collect_interval_tree_x n x2;
            collect_interval_tree_x n x3;
            ((fun n ->
              if n = 4
              then Testify_runtime.Collect.int n
              else (fun _ -> []))) n x4])) n x1 in
  Testify_runtime.increasing ((collect_interval_tree_x 1) x) &&
    Testify_runtime.increasing ((collect_interval_tree_x 2) x) &&
      Testify_runtime.increasing ((collect_interval_tree_x 3) x) &&
        Testify_runtime.increasing ((collect_interval_tree_x 4) x)

let () =
  Printexc.record_backtrace true;
  Random.self_init ();
  for i = 10 to 30 do
    for _k = 1 to 10 do
      Testify_runtime.Arbg.size := i*1000;
      let tstart = Unix.gettimeofday () in
      let size, _ = gen_itv_tree (Random.get_state ()) in
      let tend = Unix.gettimeofday () in
      Format.printf "boltz %d %f\n" size (tend -. tstart);
      Format.print_flush ();
    done;
  done;
  

