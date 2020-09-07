type pos_int = int[@satisfying ((<) 0)]
type neg_int = int[@satisfying ((>) 0)]

type 'a nonemptylist = 'a list[@satisfying (fun l -> l <> [])]
