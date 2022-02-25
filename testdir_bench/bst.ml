type bst = Node of bst * (int[@collect]) * bst | Leaf
[@@satisfying increasing]

let gen_bst =
  let rec of_arbogen_bst arbg queue rs =
    match arbg with
    | Arbogen.Tree.Label ("bst", [Tuple []; child]) -> (
      match child with
      | Arbogen.Tree.Label ("Node", [x1; x2; x3]) ->
          let x1, x2, x3 =
            (fun queue rs ->
              let x1 = of_arbogen_bst x1 queue rs in
              let x2 = Testify_runtime.Arbg.to_int x2 queue rs in
              let x3 = of_arbogen_bst x3 queue rs in
              (x1, x2, x3) )
              queue rs
          in
          Node (x1, x2, x3)
      | Arbogen.Tree.Label ("Leaf", []) -> Leaf
      | _ -> failwith "Ill-formed arbogen tree" )
    | _ -> failwith "Ill-formed arbogen tree"
  in
  fun rs ->
    let wg =
      let open Arbogen.Boltzmann.WeightedGrammar in
      { names= [|"bst"; "Node"; "Leaf"; "@collect"|]
      ; rules=
          [| Union
               [ (0.499977638879, Product [Z 1; Ref 1])
               ; (0.500022361122, Product [Z 1; Ref 2]) ]
           ; Product [Ref 0; Ref 3; Ref 0]
           ; Z 0
           ; Z 0 |] }
    in
    let tree = Testify_runtime.Arbg.generate wg "bst" rs in
    let nb_collect = Testify_runtime.Arbg.count_collect tree in
    let queue =
      (fun n -> [|Testify_runtime.Sicstus.increasing_list n|]) nb_collect
    in
    nb_collect, of_arbogen_bst tree queue rs

let gen_bst_timings =
  let rec of_arbogen_bst arbg queue rs =
    match arbg with
    | Arbogen.Tree.Label ("bst", [Tuple []; child]) -> (
      match child with
      | Arbogen.Tree.Label ("Node", [x1; x2; x3]) ->
          let x1, x2, x3 =
            (fun queue rs ->
              let x1 = of_arbogen_bst x1 queue rs in
              let x2 = Testify_runtime.Arbg.to_int x2 queue rs in
              let x3 = of_arbogen_bst x3 queue rs in
              (x1, x2, x3) )
              queue rs
          in
          Node (x1, x2, x3)
      | Arbogen.Tree.Label ("Leaf", []) -> Leaf
      | _ -> failwith "Ill-formed arbogen tree" )
    | _ -> failwith "Ill-formed arbogen tree"
  in
  fun rs ->
    let wg =
      let open Arbogen.Boltzmann.WeightedGrammar in
      { names= [|"bst"; "Node"; "Leaf"; "@collect"|]
      ; rules=
          [| Union
               [ (0.499977638879, Product [Z 1; Ref 1])
               ; (0.500022361122, Product [Z 1; Ref 2]) ]
           ; Product [Ref 0; Ref 3; Ref 0]
           ; Z 0
           ; Z 0 |] }
    in
    let tstart = Unix.gettimeofday () in
    let tree = Testify_runtime.Arbg.generate wg "bst" rs in
    let tboltz = (Unix.gettimeofday ()) -. tstart in
    let nb_collect = Testify_runtime.Arbg.count_collect tree in
    let tstart = Unix.gettimeofday () in
    let queue =
      (fun n -> [|Testify_runtime.Sicstus.increasing_list n|]) nb_collect
    in
    let tsicstus = (Unix.gettimeofday ()) -. tstart in
    Format.printf "versus %d %f %f\n" nb_collect tboltz tsicstus;
    nb_collect, of_arbogen_bst tree queue rs

let gen_arbitrary_bst =
  let rec of_arbogen_bst arbg queue rs =
    match arbg with
    | Arbogen.Tree.Label ("bst", [Tuple []; child]) -> (
      match child with
      | Arbogen.Tree.Label ("Node", [x1; x2; x3]) ->
          let x1, x2, x3 =
            (fun queue rs ->
              let x1 = of_arbogen_bst x1 queue rs in
              let x2 = Testify_runtime.Arbg.to_int x2 queue rs in
              let x3 = of_arbogen_bst x3 queue rs in
              (x1, x2, x3) )
              queue rs
          in
          Node (x1, x2, x3)
      | Arbogen.Tree.Label ("Leaf", []) -> Leaf
      | _ -> failwith "Ill-formed arbogen tree" )
    | _ -> failwith "Ill-formed arbogen tree"
  in
  fun rs ->
    let wg =
      let open Arbogen.Boltzmann.WeightedGrammar in
      { names= [|"bst"; "Node"; "Leaf"; "@collect"|]
      ; rules=
          [| Union
               [ (0.499977638879, Product [Z 1; Ref 1])
               ; (0.500022361122, Product [Z 1; Ref 2]) ]
           ; Product [Ref 0; Ref 3; Ref 0]
           ; Z 0
           ; Z 0 |] }
    in
    let tree = Testify_runtime.Arbg.generate wg "bst" rs in
    let nb_collect = Testify_runtime.Arbg.count_collect tree in
    let queue =
      (fun n -> [| List.init n (fun _ ->  QCheck.Gen.int rs)|]) nb_collect
    in
    of_arbogen_bst tree queue rs


let spec_binary_tree x =
  let rec collect_binary_tree n = function
    | Node (x1, x2, x3) ->
        (fun n (x1, x2, x3) ->
          List.flatten
            [ collect_binary_tree n x1
            ; (fun n ->
                if n = 0 then Testify_runtime.Collect.int n else fun _ -> []
                )
                n x2
            ; collect_binary_tree n x3 ] )
          n (x1, x2, x3)
    | Leaf -> []
  in
  (fun x -> Testify_runtime.increasing ((collect_binary_tree 0) x)) x

exception Stop

let gen_reject_bst count =
  try
    for i = 1 to count do
      ignore i;
      if Random.get_state () |> gen_arbitrary_bst |> spec_binary_tree then
        raise Stop
    done;
    false
  with Stop -> true

let () =
  Printexc.record_backtrace true;
  Random.self_init ();
  Format.printf "\n====bst====\n";
  Format.printf "targeted_size average_size nb_generated average_time\n";
  let allowed_time = 1. in
  List.iter (fun i ->
      Testify_runtime.Arbg.size := i*2;
      let ttotal = ref 0. in
      let nb_generated = ref 0 in
      let size_generated = ref 0 in
      try
        while true do
          let tstart = Unix.gettimeofday () in
          let size, _ = gen_bst (Random.get_state ()) in
          let tend = Unix.gettimeofday () in
          if !ttotal +. tend -. tstart > allowed_time then
            raise Exit;
          size_generated := !size_generated + size;
          incr nb_generated;
          ttotal := !ttotal +. tend -. tstart;
        done;
      with Exit ->
            begin
              Format.printf "%d %f %d %f\n" i ((float_of_int !size_generated) /. (float_of_int !nb_generated)) !nb_generated (!ttotal /. (float_of_int !nb_generated));
              Format.print_flush ()
            end)
    [10;100;1000;10000]



(* let () = *)
(*   Random.self_init (); *)
(*   Testify_runtime.count := 1; *)
(*   (\* spec_binary_tree (gen_arbitrary_bst (Random.get_state ())) |> ignore; *\) *)
(*   print_newline (); *)
(*   for i = 1 to 20 do *)
(*     Testify_runtime.Arbg.size := i ; *)
(*     let tstart = Unix.gettimeofday () in *)
(*     let res = gen_reject_bst (i*1000) in *)
(*     let tend = Unix.gettimeofday () in *)
(*     Format.printf "rejection %d %f %b\n" i (tend -. tstart) res; *)
(*   done; *)

(*   for i = 1 to 20 do *)
(*     Testify_runtime.Arbg.size := i ; *)
(*     let tstart = Unix.gettimeofday () in *)
(*     gen_bst (Random.get_state ()) |> ignore; *)
(*     let tend = Unix.gettimeofday () in *)
(*     Format.printf "boltz %d %f\n" i (tend -. tstart); *)
(*   done; *)
  
(*   for i = 1 to 40 do *)
(*     Testify_runtime.Arbg.size := i*1000 ; *)
(*     let tstart = Unix.gettimeofday () in *)
(*     let size, _ = gen_bst (Random.get_state ()) in *)
(*     let tend = Unix.gettimeofday () in *)
(*     Format.printf "boltz %d %f\n" size (tend -. tstart); *)
(*     Format.print_flush (); *)
(*   done; *)

(*   for i = 1 to 40 do *)
(*     Testify_runtime.Arbg.size := i*1000 ; *)
(*     gen_bst_timings (Random.get_state ()) |> ignore; *)
(*     Format.print_flush (); *)
(*   done *)
