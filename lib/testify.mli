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

val over_approx :
  ?subscribe:bool -> count:int ->
  name:string ->
  'a QCheck.arbitrary ->
  ('a -> 'a) ->
  ('b -> 'b) -> ('a -> 'b -> bool) -> ('a -> 'b) -> unit

val over_approx2 :
  ?subscribe:bool -> count:int ->
  name:string ->
  'a QCheck.arbitrary ->
  ('a -> 'a -> 'a) ->
  ('b -> 'b -> 'b) -> ('a -> 'b -> bool) -> ('a -> 'b) -> unit

val run : unit -> unit
