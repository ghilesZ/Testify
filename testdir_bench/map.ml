type map = Node of map * (int[@collect]) * int * map | Leaf
[@@satisfying increasing]

let gen_map =
  let rec of_arbogen_map arbg queue rs =
    match arbg with
    | Arbogen.Tree.Label ("map", [Tuple []; child]) -> (
      match child with
      | Arbogen.Tree.Label ("Node", [x1; x2; x3; x4]) ->
          let x1, x2, x3, x4 =
            (fun queue rs ->
              let x1 = of_arbogen_map x1 queue rs in
              let x2 = Testify_runtime.Arbg.to_int x2 queue rs in
              let x3 = Testify_runtime.Arbg.to_int x3 queue rs in
              let x4 = of_arbogen_map x4 queue rs in
              (x1, x2, x3, x4) )
              queue rs
          in
          Node (x1, x2, x3, x4)
      | Arbogen.Tree.Label ("Leaf", []) -> Leaf
      | _ -> failwith "Ill-formed arbogen tree" )
    | _ -> failwith "Ill-formed arbogen tree"
  in
  fun rs ->
    let wg =
      let open Arbogen.Boltzmann.WeightedGrammar in
      { names= [|"map"; "Node"; "Leaf"; "@collect"|]
      ; rules=
          [| Union
               [ (0.499977638879, Product [Z 1; Ref 1])
               ; (0.500022361122, Product [Z 1; Ref 2]) ]
           ; Product [Ref 0; Ref 3; Z 0; Ref 0]
           ; Z 0
           ; Z 0 |] }
    in
    let tree = Testify_runtime.Arbg.generate wg "map" rs in
    let nb_collect = Testify_runtime.Arbg.count_collect tree in
    let queue =
      (fun n -> [|Testify_runtime.Sicstus.increasing_list n|]) nb_collect
    in
    (nb_collect, of_arbogen_map tree queue rs)

let () =
  Printexc.record_backtrace true ;
  Random.self_init () ;
  Format.printf "\n====map====\n" ;
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
          let size, _ = gen_map (Random.get_state ()) in
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
