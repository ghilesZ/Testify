(* holder for test suites *)
let suite = ref []

let commut ?subscribe:(s=true) ~count ~name gen f =
  let t = QCheck.Test.make ~count ~name
    (QCheck.pair gen gen)
    (fun (i,j) -> f i j = f j i)
  in
  if s then suite := (t::!suite) else QCheck.Test.check_exn t

let assoc ?subscribe:(s=true) ~count ~name gen f =
  let t = QCheck.Test.make ~count ~name
    (QCheck.triple gen gen gen)
    (fun (i,j,k) -> f (f i j) k = f i (f j k))
  in if s then suite := (t::!suite) else QCheck.Test.check_exn t

let distrib_left ?subscribe:(s=true) ~count ~name gen f g =
  let t = QCheck.Test.make ~count ~name
    (QCheck.triple gen gen gen)
    (fun (i,j,k) -> f i (g j k) = g (f i j) (f i k))
  in if s then suite := (t::!suite) else QCheck.Test.check_exn t

let distrib_right ?subscribe:(s=true) ~count ~name gen f g =
  let t = QCheck.Test.make ~count ~name
    (QCheck.triple gen gen gen)
    (fun (i,j,k) -> f (g i j) k = g (f i k) (f j k))
  in if s then suite := (t::!suite) else QCheck.Test.check_exn t

let distrib ?subscribe:(s=true) ~count ~name gen f g =
  let t = QCheck.Test.make ~count ~name
    (QCheck.triple gen gen gen)
    (fun (i,j,k) -> f i (g j k) = g (f i j) (f i k) && f (g i j) k = g (f i k) (f j k))
  in if s then suite := (t::!suite) else QCheck.Test.check_exn t


let increasing ?subscribe:(s=true) ~count ~name gen f compare =
  let t = QCheck.Test.make ~count ~name
    (QCheck.pair gen gen)
    (fun (i,j) -> (compare i j) * (compare (f i) (f j)) > 0)
  in if s then suite := (t::!suite) else QCheck.Test.check_exn t

let decreasing ?subscribe:(s=true) ~count ~name gen f compare =
  let t = QCheck.Test.make ~count ~name
    (QCheck.pair gen gen)
    (fun (i,j) -> (compare i j) * (compare (f i) (f j)) < 0)
  in if s then suite := (t::!suite) else QCheck.Test.check_exn t


let neutral_left ?subscribe:(s=true) ~count ~name gen f neutral =
  let t = QCheck.Test.make ~count ~name
    gen
    (fun i -> f neutral i = i)
  in if s then suite := (t::!suite) else QCheck.Test.check_exn t

let neutral_right ?subscribe:(s=true) ~count ~name gen f neutral =
  let t = QCheck.Test.make ~count ~name
    gen
    (fun i -> f i neutral = i)
  in if s then suite := (t::!suite) else QCheck.Test.check_exn t

let neutral ?subscribe:(s=true) ~count ~name gen f neutral =
  let t = QCheck.Test.make ~count ~name
    gen
    (fun i -> f i neutral = i && f neutral i = i)
  in if s then suite := (t::!suite) else QCheck.Test.check_exn t

let absorb_left ?subscribe:(s=true) ~count ~name gen f absorb =
  let t = QCheck.Test.make ~count ~name
    gen
    (fun i -> f absorb i = absorb)
  in if s then suite := (t::!suite) else QCheck.Test.check_exn t

let absorb_right ?subscribe:(s=true) ~count ~name gen f absorb =
  let t = QCheck.Test.make ~count ~name
    gen
    (fun i -> f i absorb = absorb)
  in if s then suite := (t::!suite) else QCheck.Test.check_exn t

let absorb ?subscribe:(s=true) ~count ~name gen f absorb =
  let t = QCheck.Test.make ~count ~name
    gen
    (fun i -> f i absorb = absorb && f absorb i = absorb)
  in if s then suite := (t::!suite) else QCheck.Test.check_exn t

(* Galois connection stuff *)
(***************************)

type ('a,'b) gc = {
    alpha : Random.State.t -> 'a; (* abstract value generator *)
    r_gamma : 'a -> 'b;           (* concrete value generator, wrt an abstract element *)
    in_gamma : 'a -> 'b -> bool;
    a_printer : Format.formatter -> 'a -> unit;
    g_printer : Format.formatter -> 'b -> unit
  }

let make_gc alpha r_gamma in_gamma a_printer g_printer = {
    alpha; r_gamma; in_gamma; a_printer; g_printer
  }

(* generates one absract value 'a' and one concrete value 'c'
   s.t 'c \in \gamma(a)' *)
let gc_gen gc : ('a * 'b) QCheck.Gen.t = fun st ->
  let abs = gc.alpha st in
  let conc = gc.r_gamma abs in
  abs,conc

let over_approx ?subscribe:(s=true) ~count ~name (gc:('a,'b) gc)
      (f: 'a -> 'a)
      (g:'b -> 'b)
      (f_name:string)
      (g_name:string)
  =
  let print (a,c) =
    Format.asprintf "%s(%a) not included in %s(%a)" g_name gc.g_printer c f_name gc.a_printer a
  in
  let t = QCheck.Test.make ~count ~name
            (QCheck.make ~print (gc_gen gc))
            (fun (i,j) -> gc.in_gamma (f i) (g j))
  in if s then suite := (t::!suite) else QCheck.Test.check_exn t

let over_approx2 ?subscribe:(s=true) ~count ~name (gc:('a,'b) gc)
      (f: 'a -> 'a -> 'a)
      (g: 'b -> 'b -> 'b)
      (a_name:string)
      (g_name:string) =
  let print ((a1,c1),(a2,c2)) =
    let a_res = f a1 a2 in
    let c_res = g c1 c2 in
    let open Format in
    let l1 = asprintf "%a not in %a" gc.g_printer c_res gc.a_printer a_res in
    let l2 = asprintf "with %a = %s(%a,%a)" gc.g_printer c_res g_name gc.g_printer c1 gc.g_printer c2 in
    let l3 = asprintf "and %a = %s(%a,%a)" gc.a_printer a_res a_name gc.a_printer a1 gc.a_printer a2 in
    let l4 = asprintf "and %a were generated from %a" gc.g_printer c1 gc.a_printer a1 in
    let l5 = asprintf "and %a were generated from %a" gc.g_printer c2 gc.a_printer a2 in
    l1^"\n"^l2^"\n"^l3^"\n"^l4^"\n"^l5
  in
  let t = QCheck.Test.make ~count ~name
            (QCheck.make ~print (fun st -> (gc_gen gc) st, (gc_gen gc) st))
            (fun ((a1,c1),(a2,c2)) ->
              let abs = f a1 a2 in
              let conc = g c1 c2 in
              gc.in_gamma abs conc)
  in if s then suite := (t::!suite) else QCheck.Test.check_exn t

let run () = ignore (QCheck_runner.run_tests ~colors:true ~verbose:true (!suite))
