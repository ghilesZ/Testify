(** Logging *)

(** {2 Warnings and errors} *)

let alert_ prefix = Format.kasprintf (Format.eprintf "%s: %s@." prefix)

let error args = alert_ "ERROR" args

let warn args = alert_ "WARNING" args

(** {2 Log file generation} *)

let log = ref false

let format : Format.formatter option ref = ref None

let get_output () =
  match !format with None -> failwith "ouput for log not set" | Some f -> f

let print x =
  if !log then Format.fprintf (get_output ()) x
  else Format.ifprintf Format.std_formatter x

let set_output () =
  log := true ;
  let file = "log.markdown" in
  let oc = open_out file in
  at_exit (fun () -> close_out oc) ;
  format := Some (Format.formatter_of_out_channel oc)

let type_decl ((_, typs) as td) =
  let open Helper in
  let open Migrate_parsetree.Ast_410.Parsetree in
  print "### Declaration of type(s)\n" ;
  print "- source:\n\n```ocaml@.%a\n```\n\n" print_td td ;
  List.iter
    (fun td ->
      print "- Kind: %s%s%s\n"
        ( if
          Option.is_none
            (get_attribute_pstr "satisfying" td.ptype_attributes)
        then ""
        else "constrained " )
        (if td.ptype_params = [] then "" else "polymorphic ")
        ( match td.ptype_kind with
        | Ptype_abstract -> "abstract type"
        | Ptype_variant _ -> "sum type"
        | Ptype_record _ -> "record type"
        | Ptype_open -> "extensible type" ) )
    typs
