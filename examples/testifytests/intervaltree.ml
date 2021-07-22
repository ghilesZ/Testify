type t = {lbound: float; rbound: float; value: float}
[@@s.t lbound <=. value && value <=. rbound]
