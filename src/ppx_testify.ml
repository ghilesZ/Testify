let args =
  [ ( "-nb"
    , Arg.Int (( := ) Satisfying.number)
    , "Sets the number of runs per test" )
  ; ("-log", Arg.Unit Log.set_output, "Enables the generation of a report")
  ; ("-seed", Arg.Int Satisfying.set_seed, "Sets the random seed")
  ; ( "-cover_size"
    , Arg.Int Gegen.set_size
    , "Sets the maximum size of a cover seed" )
  ; ( "-domain"
    , Arg.String Gegen.set_dom
    , "Sets the abstract domain used for solving" ) ]

(* registering the mappers *)
let () =
  let open Migrate_parsetree in
  Driver.register ~name:"ppx_such_that" ~args:[] Versions.ocaml_410
    (fun _config _cookies -> Such_that.mapper) ;
  Driver.register ~name:"ppx_satisfying" ~args Versions.ocaml_410
    (fun _config _cookies -> Satisfying.mapper)
