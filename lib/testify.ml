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

let over_approx ?subscribe:(s=true) ~count ~name gen (f: 'a -> 'a) (g:'b -> 'b)
      (in_gamma : 'a -> 'b -> bool) (rand_gamma: 'a -> 'b) =
  let t = QCheck.Test.make ~count ~name
    gen
    (fun i -> in_gamma (f i) (g (rand_gamma i)))
  in if s then suite := (t::!suite) else QCheck.Test.check_exn t

let over_approx2 ?subscribe:(s=true) ~count ~name gen
      (f: 'a -> 'a -> 'a)
      (g:'b -> 'b -> 'b)
      (in_gamma : 'a -> 'b -> bool)
      (rand_gamma: 'a -> 'b) =
  let t = QCheck.Test.make ~count ~name
    (QCheck.pair gen gen)
    (fun (i,j) ->
      let abs = f i j in
      let conc = g (rand_gamma i) (rand_gamma j) in
      in_gamma abs conc)
  in if s then suite := (t::!suite) else QCheck.Test.check_exn t

let run () = ignore (QCheck_runner.run_tests ~colors:true ~verbose:true (!suite))
