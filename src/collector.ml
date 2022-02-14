type t =
  | Skip  (** dont consume anything *)
  | Consume of int  (** consume in the nth queue*)
  | Unknown  (** Unknown *)
