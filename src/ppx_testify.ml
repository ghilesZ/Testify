let args =
  let open Satisfying in
  [ ("-nb", Arg.Int (( := ) number), "Sets the number of runs per test")
  ; ("-log", Arg.Set log, "Enables the generation of a report") ]

(* registering the mappers *)
let () =
  let open Migrate_parsetree in
  Driver.register ~name:"ppx_such_that" ~args:[] Versions.ocaml_410
    (fun _config _cookies -> Such_that.mapper) ;
  Driver.register ~name:"ppx_satisfying" ~args Versions.ocaml_410
    (fun _config _cookies -> Satisfying.mapper)
