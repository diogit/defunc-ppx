type t =
  | E 
  | N of t * t 
type kont =
  | K0 
  | K1 of t * kont 
  | K2 of kont * int 
let rec main t = h_cps t K0

and h_cps t k =
  match t with | E  -> apply k 0 | N ((l : t),(r : t)) -> h_cps l (K1 (r, k))

and apply k arg =
  match k with
  | K0  -> let x = arg  in x
  | K1 (r,k) -> let hl = arg  in h_cps r (K2 (k, hl))
  | K2 (k,hl) -> let hr = arg  in apply k (1 + (max hl hr))

