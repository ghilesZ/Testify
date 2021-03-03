let args =
  [("-nb", Arg.Int Satisfying.set_number, "Sets the number of runs per test")]

(* registering the mappers *)
let () =
  let open Migrate_parsetree in
  Driver.register ~name:"ppx_such_that" ~args:[] Versions.ocaml_410
    (fun _config _cookies -> Such_that.mapper) ;
  Driver.register ~name:"ppx_satisfying" ~args Versions.ocaml_410
    (fun _config _cookies -> Satisfying.mapper)
