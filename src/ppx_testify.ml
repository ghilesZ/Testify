let args =
  let open Satisfying in
  [ ("-nb", Arg.Int (( := ) number), "Sets the number of runs per test")
  ; ("-log", Arg.Set Log.log, "Enables the generation of a report")
  ; ("-seed", Arg.Int set_seed, "Sets the random seed")
  ; ( "-cover_size"
    , Arg.Int Gegen.set_size
    , "Sets the maximum size of a cover seed" )
  ; ( "-bench"
    , Arg.String (( := ) Gegen.bench)
    , "Enables the measure of the generation rate" )
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
