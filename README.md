Testify
Testify is a syntactic extension that features type driven code
generation to automatically generate test for your programs. It
allows you to attach a property to a given type t and use the explicit
type annotations of your program to generate tests for the values of type t, as in the following example.

type itv = int * int [@satisfying (fun (x,y) -> x <= y)]

let add (i1:itv) (i2:itv) : itv =
  ((fst i1) + (fst i2)), ((snd i1) + (snd i2))
which is rewritten into:

type itv = int * int [@satisfying (fun (x,y) -> x <= y)]

let add (i1:itv) (i2:itv) : itv =
  ((fst i1) + (fst i2)), ((snd i1) + (snd i2))

let _ =
    let open QCheck in
    Test.make ~count:1000
              ~name:"Test : add according to fun (x, y) -> x <= y"
              (QCheck.make
                (QCheck.Gen.pair
                  (QCheck.find_example ~f:(fun (x, y) -> x <= y)
                                       (QCheck.Gen.pair QCheck.Gen.int QCheck.Gen.int))
                  (QCheck.find_example ~f:(fun (x, y) -> x <= y)
                                       (QCheck.Gen.pair QCheck.Gen.int QCheck.Gen.int))))
               (fun (x1, x2) -> (fun (x, y) -> x <= y) (add x1 x2))

As you noticed, Testify uses the wonderful QCheck library as a testing
framework.

How is it done?
Testifies features an automatic derivation of QCheck’s generators for most basic types and uses those to randomly generates inputs for each function whose return type was attached a generator.