type t = Unknown | Infinite | Finite of Z.t

(** {3 Shorthands to build values} *)

let finite (n : Z.t) = Finite n

let of_int n = finite (Z.of_int n)

(** {3 Shorthands to access values} *)

let as_z = function
  | Finite n -> n
  | Infinite | Unknown -> invalid_arg "Card.as_z"

let is_finite = function Finite _ -> true | Infinite | Unknown -> false

(** {3 arithmetics} *)

let add c1 c2 =
  match (c1, c2) with
  | Infinite, _ | _, Infinite -> Infinite
  | Unknown, _ | _, Unknown -> Unknown
  | Finite f1, Finite f2 -> Finite (Z.add f1 f2)

let mul c1 c2 =
  match (c1, c2) with
  | Infinite, _ | _, Infinite -> Infinite
  | Unknown, _ | _, Unknown -> Unknown
  | Finite f1, Finite f2 -> Finite (Z.mul f1 f2)

let sum cs = List.fold_left add (of_int 0) cs

let product cs = List.fold_left add (of_int 1) cs

(** {3 Pretty printing} *)

let pp fmt = function
  | Unknown -> Format.pp_print_string fmt "unknown"
  | Infinite -> Format.pp_print_string fmt "infinite"
  | Finite n -> Helper.print_bigint fmt n
