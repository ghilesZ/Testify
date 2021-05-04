(* log file generation *)
let log = ref false

let fn = ref ""

(* name of the module being rewritten *)
let format : Format.formatter option ref = ref None

let get_output () =
  match !format with None -> failwith "ouput for log not set" | Some f -> f

let set_output s =
  if !log then
    match !format with
    | None ->
        fn := s ;
        let s = Filename.(chop_extension (basename s)) in
        let fn = s ^ ".markdown" in
        let oc = open_out fn in
        at_exit (fun () -> close_out oc) ;
        format := Some (Format.formatter_of_out_channel oc)
    | Some _ -> ()

let print x =
  if !log then Format.fprintf (get_output ()) x
  else Format.ifprintf Format.std_formatter x
