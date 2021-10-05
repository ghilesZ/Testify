type pos = (int[@satisfying fun x -> x > 0])

module M = struct
  type t = (int[@satisfying fun x -> x <= 1000])

  let one : t = -1

  let pred (x : pos) : pos = x - 1
end

let two : pos = 2

let x : M.t = 4
