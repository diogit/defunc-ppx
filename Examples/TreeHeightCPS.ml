type t = E | N of t * t
let rec h_cps t k = 
  match t with
  | E -> k 0
  | N (l, r) -> 
      h_cps l (fun hl ->
      h_cps r (fun hr -> k (1 + max hl hr))) 