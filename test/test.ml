type t = E | N of t * t

let %defun rec main t =
  h_cps t (fun [@K0] x -> x) (* FV : K0 |-> { } *)

and h_cps (t: t) (k: int -> 'a) =
  match t with
  | E -> k 0
  | N ((l: t), (r: t)) ->
    h_cps l (fun [@K1] (hl: int) -> (* FV: K1 |-> { r: t; k: int -> 'a } *)
    h_cps r (fun [@K2] (hr: int) -> (* FV: K2 |-> { k: int -> 'a; hl: int } *)
            k (1 + max hl hr)))
            
let %print x = ()

  