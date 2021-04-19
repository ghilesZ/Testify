(* log file generation *)
let log = ref false

(* name of the module being rewritten *)
let filename : Format.formatter option ref = ref None

let get_output () =
  match !filename with
  | None -> failwith "ouput for log not set"
  | Some f -> f

let set_output s =
  if !log then
    match !filename with
    | None ->
        let s = Filename.(chop_extension (basename s)) ^ ".log" in
        filename := Some (Format.formatter_of_out_channel (open_out s))
    | Some _ -> ()

let print x =
  if !log then Format.fprintf (get_output ()) x
  else Format.ifprintf Format.std_formatter x
