type interval_tree_x =
  | LeafX
  | NodeX of
      (int[@collect 1])
      * interval_tree_y
      * interval_tree_y
      * (int[@collect 2])
[@@satisfying fun x -> increasing x 1 && increasing x 2]

and interval_tree_y =
  | LeafY
  | NodeY of
      (int[@collect 3])
      * interval_tree_x
      * interval_tree_x
      * (int[@collect 4])
[@@satisfying fun x -> increasing x 3 && increasing x 4]

let gen_quad =
  let rec of_arbogen_interval_tree_x arbg queue rs =
    match arbg with
    | Arbogen.Tree.Label ("interval_tree_x", [Tuple []; child]) -> (
      match child with
      | Arbogen.Tree.Label ("LeafX", []) -> LeafX
      | Arbogen.Tree.Label ("NodeX", [x1; x2; x3; x4]) ->
          let x1, x2, x3, x4 =
            (fun queue rs ->
              let x1 = Testify_runtime.Arbg.to_int x1 queue rs in
              let x2 = of_arbogen_interval_tree_y x2 queue rs in
              let x3 = of_arbogen_interval_tree_y x3 queue rs in
              let x4 = Testify_runtime.Arbg.to_int x4 queue rs in
              (x1, x2, x3, x4) )
              queue rs
          in
          NodeX (x1, x2, x3, x4)
      | _ -> failwith "Ill-formed arbogen tree" )
    | _ -> failwith "Ill-formed arbogen tree"
  and of_arbogen_interval_tree_y arbg queue rs =
    match arbg with
    | Arbogen.Tree.Label ("interval_tree_y", [Tuple []; child]) -> (
      match child with
      | Arbogen.Tree.Label ("LeafY", []) -> LeafY
      | Arbogen.Tree.Label ("NodeY", [x1; x2; x3; x4]) ->
          let x1, x2, x3, x4 =
            (fun queue rs ->
              let x1 = Testify_runtime.Arbg.to_int x1 queue rs in
              let x2 = of_arbogen_interval_tree_x x2 queue rs in
              let x3 = of_arbogen_interval_tree_x x3 queue rs in
              let x4 = Testify_runtime.Arbg.to_int x4 queue rs in
              (x1, x2, x3, x4) )
              queue rs
          in
          NodeY (x1, x2, x3, x4)
      | _ -> failwith "Ill-formed arbogen tree" )
    | _ -> failwith "Ill-formed arbogen tree"
  in
  fun rs ->
    let wg =
      let open Arbogen.Boltzmann.WeightedGrammar in
      { names=
          [| "interval_tree_x"
           ; "LeafX"
           ; "NodeX"
           ; "interval_tree_y"
           ; "LeafY"
           ; "NodeY"
           ; "@collect" |]
      ; rules=
          [| Union
               [ (0.500022361122, Product [Z 1; Ref 1])
               ; (0.499977638879, Product [Z 1; Ref 2]) ]
           ; Z 0
           ; Product [Ref 6; Ref 3; Ref 3; Ref 6]
           ; Union
               [ (0.500022361122, Product [Z 1; Ref 4])
               ; (0.499977638879, Product [Z 1; Ref 5]) ]
           ; Z 0
           ; Product [Ref 6; Ref 0; Ref 0; Ref 6]
           ; Z 0 |] }
    in
    let tree = Testify_runtime.Arbg.generate wg "interval_tree_x" rs in
    let nb_collect = Testify_runtime.Arbg.count_collect tree in
    let queue =
      (fun n -> [|Testify_runtime.Sicstus.increasing_list n|]) nb_collect
    in
    (nb_collect, of_arbogen_interval_tree_x tree queue rs)

let () =
  Printexc.record_backtrace true ;
  Random.self_init () ;
  Format.printf "\n====quadtree====\n" ;
  Format.printf "targeted_size average_size nb_generated average_time\n" ;
  let allowed_time = 1. in
  List.iter
    (fun i ->
      Testify_runtime.Arbg.size := i ;
      let ttotal = ref 0. in
      let nb_generated = ref 0 in
      let size_generated = ref 0 in
      try
        while true do
          let tstart = Unix.gettimeofday () in
          let size, _ = gen_quad (Random.get_state ()) in
          let tend = Unix.gettimeofday () in
          if !ttotal +. tend -. tstart > allowed_time then raise Exit ;
          size_generated := !size_generated + size ;
          incr nb_generated ;
          ttotal := !ttotal +. tend -. tstart
        done
      with Exit ->
        Format.printf "%d %f %d %f\n" i
          (float_of_int !size_generated /. float_of_int !nb_generated)
          !nb_generated
          (!ttotal /. float_of_int !nb_generated) ;
        Format.print_flush () )
    [10; 100; 1000; 10000]
