open Testify
let add a b = a - b[@@gen QCheck.int][@@commut ]
let _ =
  commut ~count:1000
    ~name:"commutativity test of add in file examples/arith.ml" QCheck.int
    add
