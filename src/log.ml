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
        let s = Filename.(chop_extension (basename s)) in
        let file = s ^ ".markdown" in
        let oc = open_out file in
        at_exit (fun () -> close_out oc) ;
        format := Some (Format.formatter_of_out_channel oc) ;
        print "# File **%s**\n" s
    | Some _ -> ()
