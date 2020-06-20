let commut ~count ~name gen f =
  QCheck.Test.make ~count ~name
    (QCheck.pair gen gen)
    (fun (i,j) -> f i j = f j i)
  |> QCheck.Test.check_exn

let assoc ~count ~name gen f =
  QCheck.Test.make ~count ~name
    (QCheck.triple gen gen gen)
    (fun (i,j,k) -> f (f i j) k = f i (f j k))
  |> QCheck.Test.check_exn

let distrib_left ~count ~name gen f g =
  QCheck.Test.make ~count ~name
    (QCheck.triple gen gen gen)
    (fun (i,j,k) -> f i (g j k) = g (f i j) (f i k))
  |> QCheck.Test.check_exn

let distrib_right ~count ~name gen f g =
  QCheck.Test.make ~count ~name
    (QCheck.triple gen gen gen)
    (fun (i,j,k) -> f (g i j) k = g (f i k) (f j k))
  |> QCheck.Test.check_exn

let distrib ~count ~name gen f g =
  QCheck.Test.make ~count ~name
    (QCheck.triple gen gen gen)
    (fun (i,j,k) -> f i (g j k) = g (f i j) (f i k) && f (g i j) k = g (f i k) (f j k))
  |> QCheck.Test.check_exn

let increasing ~count ~name gen f compare =
  QCheck.Test.make ~count ~name
    (QCheck.pair gen gen)
    (fun (i,j) -> (compare i j) * (compare (f i) (f j)) > 0)
  |> QCheck.Test.check_exn

let decreasing ~count ~name gen f compare =
  QCheck.Test.make ~count ~name
    (QCheck.pair gen gen)
    (fun (i,j) -> (compare i j) * (compare (f i) (f j)) < 0)
  |> QCheck.Test.check_exn


let neutral_left ~count ~name gen f neutral =
  QCheck.Test.make ~count ~name
    gen
    (fun i -> f neutral i = i)
  |> QCheck.Test.check_exn

let neutral_right ~count ~name gen f neutral =
  QCheck.Test.make ~count ~name
    gen
    (fun i -> f i neutral = i)
  |> QCheck.Test.check_exn

let neutral ~count ~name gen f neutral =
  QCheck.Test.make ~count ~name
    gen
    (fun i -> f i neutral = i && f neutral i = i)
  |> QCheck.Test.check_exn

let absorb_left ~count ~name gen f absorb =
  QCheck.Test.make ~count ~name
    gen
    (fun i -> f absorb i = absorb)
  |> QCheck.Test.check_exn

let absorb_right ~count ~name gen f absorb =
  QCheck.Test.make ~count ~name
    gen
    (fun i -> f i absorb = absorb)
  |> QCheck.Test.check_exn

let absorb ~count ~name gen f absorb =
  QCheck.Test.make ~count ~name
    gen
    (fun i -> f i absorb = absorb && f absorb i = absorb)
  |> QCheck.Test.check_exn

let over_approx ~count ~name gen (f: 'a -> 'a) (g:'b -> 'b)
      (in_gamma : 'a -> 'b -> bool) (rand_gamma: 'a -> 'b) =
  QCheck.Test.make ~count ~name
    gen
    (fun i -> in_gamma (f i) (g (rand_gamma i)))
  |> QCheck.Test.check_exn

let over_approx2 ~count ~name gen
      (f: 'a -> 'a -> 'a)
      (g:'b -> 'b -> 'b)
      (in_gamma : 'a -> 'b -> bool)
      (rand_gamma: 'a -> 'b) =
  QCheck.Test.make ~count ~name
    (QCheck.pair gen gen)
    (fun (i,j) ->
      let abs = f i j in
      let conc = g (rand_gamma i) (rand_gamma j) in
      in_gamma abs conc)
  |> QCheck.Test.check_exn
