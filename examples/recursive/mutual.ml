type tree = Leaf | Node of node

and node = int * tree * tree
