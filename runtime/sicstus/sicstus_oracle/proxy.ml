let debug = ref false

let seed = ref 0

let set_seed x = seed := x

let log x =
  if !debug then (Format.printf "[proxy] " ; Format.printf x)
  else Format.ifprintf Format.std_formatter x

let out_buff = Bytes.create (1 + 2 + 2)

let in_buff = Bytes.create ((1 lsl 16) * 4)

type global_constraint =
  | Increasing_list
  | Decreasing_list
  | Increasing_strict_list
  | Decreasing_strict_list
  | Alldiff_list

let gc_opcode = function
  | Increasing_list -> '\002'
  | Decreasing_list -> '\003'
  | Increasing_strict_list -> '\004'
  | Decreasing_strict_list -> '\005'
  | Alldiff_list -> '\006'

let exit_code = '\001'

let process =
  lazy
    (let () = Unix.putenv "LD_LIBRARY_PATH" "/usr/local/sicstus4.7.1/lib" in
     let ((p_out, p_in) as process) = Unix.open_process "oracle" in
     let pid = Unix.process_pid process in
     let p_out, p_in =
       (Unix.descr_of_in_channel p_out, Unix.descr_of_out_channel p_in)
     in
     at_exit (fun () ->
         log "terminating sicstus process@." ;
         Bytes.set out_buff 0 '\001' ;
         Unix.write p_in out_buff 0 1 |> ignore ;
         Unix.waitpid [] pid |> ignore ) ;
     log "sicstus process started (pid: %d)@." pid ;
     (p_out, p_in) )

let really_read p_out n =
  let rec loop ofs =
    if ofs = n then (log "end reading@." ; ())
    else (
      log "try reading %d at ofs %d@." (n - ofs) ofs ;
      let nb = Unix.read p_out in_buff ofs (n - ofs) in
      log "read %d, %d left to read@." nb (ofs + nb) ;
      if nb = 0 then raise End_of_file else loop (ofs + nb) )
  in
  loop 0

let call_sicstus length seed gc =
  let p_out, p_in = Lazy.force process in
  Bytes.set out_buff 0 (gc_opcode gc) ;
  Bytes.set_int16_be out_buff 1 length ;
  Bytes.set_int16_be out_buff (1 + 2) seed ;
  Unix.write p_in out_buff 0 5 |> log "wrote %d@." ;
  really_read p_out (4 * length) ;
  List.init length (fun i ->
      Bytes.get_int32_le in_buff (i * 4) |> Int32.to_int )

let increasing_list ?(seed = !seed) length =
  call_sicstus length seed Increasing_list

let increasing_strict_list ?(seed = !seed) length =
  call_sicstus length seed Increasing_strict_list

let decreasing_list ?(seed = !seed) length =
  call_sicstus length seed Decreasing_list

let decreasing_strict_list ?(seed = !seed) length =
  call_sicstus length seed Decreasing_strict_list

let all_diff_list ?(seed = !seed) length =
  call_sicstus length seed Decreasing_strict_list

let test () =
  Random.self_init () ;
  let length () = Random.int (1 lsl 3) in
  let pp_list l = log "@[<v>%a@]@." Format.(pp_print_list pp_print_int) l in
  pp_list @@ increasing_list (length ()) ;
  pp_list @@ increasing_strict_list (length ()) ;
  pp_list @@ decreasing_list (length ()) ;
  pp_list @@ decreasing_strict_list (length ()) ;
  pp_list @@ all_diff_list (length ())
