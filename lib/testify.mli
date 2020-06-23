val commut :
  ?subscribe:bool -> count:int ->
  name:string -> 'a QCheck.arbitrary -> ('a -> 'a -> 'b) -> unit

val assoc :
  ?subscribe:bool -> count:int ->
  name:string -> 'a QCheck.arbitrary -> ('a -> 'a -> 'a) -> unit

val distrib_left :
  ?subscribe:bool -> count:int ->
  name:string ->
  'a QCheck.arbitrary ->
  ('a -> 'a -> 'a) -> ('a -> 'a -> 'a) -> unit

val distrib_right :
  ?subscribe:bool -> count:int ->
  name:string ->
  'a QCheck.arbitrary ->
  ('a -> 'a -> 'a) -> ('a -> 'a -> 'a) -> unit

val distrib :
  ?subscribe:bool -> count:int ->
  name:string ->
  'a QCheck.arbitrary ->
  ('a -> 'a -> 'a) -> ('a -> 'a -> 'a) -> unit

val increasing :
  ?subscribe:bool -> count:int ->
  name:string ->
  'a QCheck.arbitrary -> ('a -> 'a) -> ('a -> 'a -> int) -> unit

val decreasing :
  ?subscribe:bool -> count:int ->
  name:string ->
  'a QCheck.arbitrary -> ('a -> 'a) -> ('a -> 'a -> int) -> unit

val neutral_left :
  ?subscribe:bool -> count:int ->
  name:string ->
  'a QCheck.arbitrary -> ('b -> 'a -> 'a) -> 'b -> unit

val neutral_right :
  ?subscribe:bool -> count:int ->
  name:string ->
  'a QCheck.arbitrary -> ('a -> 'b -> 'a) -> 'b -> unit

val neutral :
  ?subscribe:bool -> count:int ->
  name:string ->
  'a QCheck.arbitrary -> ('a -> 'a -> 'a) -> 'a -> unit

val absorb_left :
  ?subscribe:bool -> count:int ->
  name:string ->
  'a QCheck.arbitrary -> ('b -> 'a -> 'b) -> 'b -> unit

val absorb_right :
  ?subscribe:bool -> count:int ->
  name:string -> 'a QCheck.arbitrary -> ('a -> 'b -> 'b) -> 'b -> unit

val absorb :
  ?subscribe:bool -> count:int ->
  name:string ->
  'a QCheck.arbitrary -> ('a -> 'a -> 'a) -> 'a -> unit

type ('a,'b) gc = {
    alpha : Random.State.t -> 'a; (* abstract value generator *)
    r_gamma : 'a -> 'b;           (* concrete value generator, wrt an abstract element *)
    in_gamma : 'a -> 'b -> bool;
    a_printer : Format.formatter -> 'a -> unit;
    g_printer : Format.formatter -> 'b -> unit
  }

val make_gc :
  (Random.State.t -> 'a) ->
  ('a -> 'b) ->
  ('a -> 'b -> bool) ->
  (Format.formatter -> 'a -> unit) ->
  (Format.formatter -> 'b -> unit) ->
  ('a, 'b) gc

val over_approx :
  ?subscribe:bool ->
  count:int ->
  name:string ->
  ('a, 'b) gc -> ('a -> 'a) -> ('b -> 'b) -> string -> string -> unit

val over_approx2 :
  ?subscribe:bool ->
  count:int ->
  name:string ->
  ('a, 'b) gc -> ('a -> 'a -> 'a) -> ('b -> 'b -> 'b) -> string -> string -> unit

val run : unit -> unit
