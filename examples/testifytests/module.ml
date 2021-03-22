type pos = (int[@satisfying fun x -> x > 0])

module M = struct
  let one : pos = -1

  let pred (x : pos) : pos = x - 1
end

let two : pos = 2
