type pos = (int[@satisfying fun x -> x >= 0])

type pos_list = Empty | Cons of pos * pos_list

type pair = pos_list * float
