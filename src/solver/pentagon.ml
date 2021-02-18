
module Num =
  struct
    type t = float
    let min_num = min_float
    let max_num = max_float
  end


module Var = String
module VMap = Map.Make(Var)
module VSet = Set.Make(Var)
  

type t = {bounds : (Num.t * Num.t) VMap.t; (* intervals where variables live *)
          upper : VSet.t VMap.t; (* upper sets of each variable *)
          lower : VSet.t VMap.t; (* lower sets of each variable *)
          vars : Var.t list} (* list of variables *)

let empty () : t = {bounds = VMap.empty;
                    upper = VMap.empty;
                    lower = VMap.empty;
                    vars = []}

let add_var (pentagon : t) (var : Var.t) ?(inf=Num.min_num) ?(sup=Num.max_num) : t =
  {pentagon with
    bounds = VMap.add var (inf,sup) pentagon.bounds;
    vars = var :: pentagon.vars}

(* add relation v1 <= v2 *)
let add_rel (pentagon : t) (v1 : Var.t) (v2 : Var.t) : t =
  let updater y = function
      None -> Some (VSet.singleton y)
    | Some s -> Some (VSet.add y s) in
  {pentagon with
    upper = VMap.update v1 (updater v2) pentagon.upper;
    lower = VMap.update v2 (updater v1) pentagon.lower}

(* let transitive_reduction (pentagon:t) : t = *)
  
  
