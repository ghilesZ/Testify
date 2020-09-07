type p_int = int [@satisfying ((<) 0)]

let abs (x:int) : p_int = if x < 0 then -x else x

let[@gen p_int] spawn = QCheck.Gen.pint
