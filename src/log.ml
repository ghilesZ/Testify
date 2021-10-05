(* log file generation *)
let log = ref false

(* name of the file being processed *)
let fn = ref ""

(* name of the module being processed *)
let mod_name = ref ""

let format : Format.formatter option ref = ref None

let get_output () =
  match !format with None -> failwith "ouput for log not set" | Some f -> f

let print x =
  if !log then Format.fprintf (get_output ()) x
  else Format.ifprintf Format.std_formatter x

let set_output s =
  if !log then
    match !format with
    | None ->
        fn := s ;
        mod_name := s ;
        let s = Filename.(chop_extension (basename s)) in
        let file = s ^ ".markdown" in
        let oc = open_out file in
        at_exit (fun () -> close_out oc) ;
        format := Some (Format.formatter_of_out_channel oc) ;
        print "# File **%s**\n" s
    | Some _ -> print "# File **%s**\n" s

let type_decl td =
  let open Helper in
  print "### Declaration of type\n" ;
  print "- ```ocaml@.@[%a@]\n```\n" print_td td ;
  print "- Kind: %s%s%s\n"
    ( if Option.is_none (get_attribute_pstr "satisfying" td.ptype_attributes)
    then ""
    else "constrained " )
    (if td.ptype_params = [] then "" else "polymorphic ")
    ( match td.ptype_kind with
    | Ptype_abstract -> "abstract type"
    | Ptype_variant _ -> "sum type"
    | Ptype_record _ -> "record type"
    | Ptype_open -> "extensible type" )
