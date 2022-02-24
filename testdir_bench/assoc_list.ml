type assoc_list =
  | Nil 
  | Cons of ((int)[@collect ]) * int * assoc_list [@@satisfying alldiff]
let id (l : assoc_list) = (l : assoc_list)

let gen_assoc_list rs =
  let rec of_arbogen_assoc_list arbg queue rs =
    match arbg with
    | Arbogen.Tree.Label ("assoc_list", (Tuple [])::child::[]) ->
       (match child with
        | Arbogen.Tree.Label ("Nil", []) -> Nil
        | Arbogen.Tree.Label ("Cons", x1::_x2::x3::[]) ->
           let (x1, _x2, x3) =
             (fun queue ->
               fun rs ->
               let x1 =
                 Testify_runtime.Arbg.to_int x1 queue rs in
               let _x2 = QCheck.Gen.int rs in
                 (* Testify_runtime.Arbg.to_int _x2 queue rs in *)
               let x3 = of_arbogen_assoc_list x3 queue rs in
               (x1, _x2, x3)) queue rs in
           Cons (x1, _x2, x3)
        | _ -> failwith "Ill-formed arbogen tree")
    | _ -> failwith "Ill-formed arbogen tree" in
  let wg =
    let open Arbogen.Boltzmann.WeightedGrammar in
    {
      names = [|"assoc_list";"Nil";"Cons";"@collect"|];
      rules =
        [|(Union
             [(0.000999001787112, (Product [Z 1; Ref 1]));
              (0.999000998213, (Product [Z 1; Ref 2]))]);
          (Z 0);
          (Product [Ref 3; Z 0; Ref 0]);
          (Z 0)|]
    } in
  let tree = Testify_runtime.Arbg.generate wg "assoc_list" rs in
  let nb_collect = Testify_runtime.Arbg.count_collect tree in
  let queue =
    (fun n -> [|(Testify_runtime.Sicstus.all_diff_list n)|])
      nb_collect in
  nb_collect, of_arbogen_assoc_list tree queue rs

let () =
  Printexc.record_backtrace true;
  Random.self_init ();
  for i = 10 to 30 do
    for _k = 1 to 10 do
      Testify_runtime.Arbg.size := i*1000;
      let tstart = Unix.gettimeofday () in
      let size, _ = gen_assoc_list (Random.get_state ()) in
      let tend = Unix.gettimeofday () in
      Format.printf "boltz %d %f\n" size (tend -. tstart);
      Format.print_flush ();
    done;
  done;


(* let rec collect_assoc_list n = *)
(*   function *)
(*   | Nil -> [] *)
(*   | Cons (x1, x2, x3) -> *)
(*      ((fun n -> *)
(*        fun (x1, x2, x3) -> *)
(*        List.flatten *)
(*          [((fun n -> *)
(*             if n = 0 *)
(*             then Testify_runtime.Collect.int n *)
(*             else (fun _ -> []))) n x1; *)
(*           Testify_runtime.Collect.int n x2; *)
(*           collect_assoc_list n x3])) n (x1, x2, x3) in *)
(*     fun x -> *)
(*     (fun x -> Testify_runtime.alldiff ((collect_assoc_list 0) x)) x) *)
