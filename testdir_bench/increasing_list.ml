type increasing_list =
  | Nil 
  | Cons of ((int)[@collect ]) * increasing_list [@@satisfying increasing]

let gen_increasing_list rs = 
  let rec of_arbogen_increasing_list arbg queue rs =
    match arbg with
    | Arbogen.Tree.Label
      ("increasing_list", (Tuple [])::child::[]) ->
       (match child with
        | Arbogen.Tree.Label ("Nil", []) -> Nil
        | Arbogen.Tree.Label ("Cons", x1::x2::[]) ->
           let (x1, x2) =
             (fun queue ->
               fun rs ->
               let x1 =
                 Testify_runtime.Arbg.to_int x1 queue rs in
               let x2 =
                 of_arbogen_increasing_list x2 queue rs in
               (x1, x2)) queue rs in
           Cons (x1, x2)
        | _ -> failwith "Ill-formed arbogen tree")
    | _ -> failwith "Ill-formed arbogen tree" in
  let wg =
    let open Arbogen.Boltzmann.WeightedGrammar in
    {
      names = [|"increasing_list";"Nil";"Cons";"@collect"|];
      rules =
        [|(Union
             [(0.000999001787112, (Product [Z 1; Ref 1]));
              (0.999000998213, (Product [Z 1; Ref 2]))]);(
            Z 0);(Product [Ref 3; Ref 0]);(Z 0)|]
    } in
  let tree =
    Testify_runtime.Arbg.generate wg "increasing_list" rs in
  let nb_collect = Testify_runtime.Arbg.count_collect tree in
  let queue =
    (fun n -> [|(Testify_runtime.Sicstus.increasing_list n)|])
      nb_collect in
  nb_collect, of_arbogen_increasing_list tree queue rs

let () =
  Printexc.record_backtrace true;
  Random.self_init ();
  Format.printf "\n====increasing_list====\n";
  Format.printf "targeted_size average_size nb_generated average_time\n";
  let allowed_time = 1. in
  List.iter (fun i ->
      Testify_runtime.Arbg.size := i;
      let ttotal = ref 0. in
      let nb_generated = ref 0 in
      let size_generated = ref 0 in
      try
        while true do
          let tstart = Unix.gettimeofday () in
          let size, _ = gen_increasing_list (Random.get_state ()) in
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


