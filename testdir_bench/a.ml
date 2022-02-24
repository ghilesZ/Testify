type increasing_list =
  | Nil 
  | Cons of ((int)[@collect ]) * increasing_list [@@satisfying increasing]
let id (l : increasing_list) = (l : increasing_list)
let () =
  Testify_runtime.add_fun 0x2710 "id"
    "File \"bench/increasing_list.ml\", line 5, characters 0-48"
    (Testify_runtime.opt_print snd)
    (Testify_runtime.opt_gen
       (fun rs ->
          let x1 =
            (let rec of_arbogen_increasing_list arbg queue rs =
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
             fun rs ->
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
               of_arbogen_increasing_list tree queue rs) rs in
          let x2 = id x1 in
          (x2,
            ((("(id " ^
                 ((let rec print_increasing_list =
                     function
                     | Nil -> "Nil"
                     | Cons (x1, x2) ->
                         "Cons" ^
                           (("(" ^
                               ((string_of_int x1) ^
                                  (", " ^ (print_increasing_list x2))))
                              ^ ")") in
                   print_increasing_list) x1))
                ^ ")")
               ^
               (" = " ^
                  ((let rec print_increasing_list =
                      function
                      | Nil -> "Nil"
                      | Cons (x1, x2) ->
                          "Cons" ^
                            (("(" ^
                                ((string_of_int x1) ^
                                   (", " ^ (print_increasing_list x2))))
                               ^ ")") in
                    print_increasing_list) x2))))))
    (Testify_runtime.sat_output
       ((let open Testify_runtime.Operators in
           let rec collect_increasing_list n =
             function
             | Nil -> []
             | Cons (x1, x2) ->
                 ((fun n ->
                     fun (x1, x2) ->
                       List.flatten
                         [((fun n ->
                              if n = 0
                              then Testify_runtime.Collect.int n
                              else (fun _ -> []))) n x1;
                         collect_increasing_list n x2])) n (x1, x2) in
           fun x ->
             (fun x ->
                Testify_runtime.increasing ((collect_increasing_list 0) x)) x)
       [@warning "-33"]))
let () = Testify_runtime.run_test ()
