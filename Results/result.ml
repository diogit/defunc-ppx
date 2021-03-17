Pexp_ident t
Seen functions: (t; t) 
Just added: (K0x, x), to the hashtbl.
Current attribute: K0
Pexp_ident x
Seen functions: (t; t) (x; x) 
Just removed: (K0, x), from the hashtbl.
Empty Stack ( , x)
Empty Stack ( , t)
Type: t: t
Type: k: int -> a
Pexp_ident t
Seen functions: (t; t) (t; t) (x; x) 
Pexp_ident k
Seen functions: (k; k) (t; t) (t; t) (x; x) 
Type: l: t
Type: r: t
Pexp_ident l
Seen functions: (l; l) (k; k) (t; t) (t; t) (x; x) 
Type: hl: int
Just added: (K1r, r), to the hashtbl.
Current attribute: K1
Pexp_ident r
Seen functions: (l; l) (k; k) (t; t) (t; t) (x; x) (r; r) 
Type: hr: int
Just added: (K2k, k), to the hashtbl.
Current attribute: K2
Just added: (K1k, k), to the hashtbl.
Current attribute: K2
Pexp_ident k
Seen functions: (k; k) (l; l) (k; k) (t; t) (t; t) (x; x) (r; r) 
Just added: (K2hl, hl), to the hashtbl.
Current attribute: K2
Just added: (K1hl, hl), to the hashtbl.
Current attribute: K2
Pexp_ident hl
Seen functions: (k; k) (l; l) (k; k) (t; t) (t; t) (hl; hl) (x; x) (r; r) 
Just added: (K2hr, hr), to the hashtbl.
Current attribute: K2
Just added: (K1hr, hr), to the hashtbl.
Current attribute: K2
Pexp_ident hr
Seen functions: (hr; hr) (k; k) (l; l) (k; k) (t; t) (t; t) (hl; hl) (x; x) (r; r) 
Just removed: (K2, hr), from the hashtbl.
Pexp_fun + Ppat_constraint, removed: K1
Just removed: (K1, hl), from the hashtbl.
Empty Stack ( , hl)
Empty Stack ( , k)
Empty Stack ( , t)
type t =
  | E 
  | N of t * t 
type kont =
  | K0 
  | K1 of t * kont 
  | K2 of kont * int 
let rec apply (k : kont) arg =
  match k with
  | K0  -> let x = arg  in x
  | K1 (r,k) ->
      let x = arg  in
      h_cps r ((fun (hr : int)  -> k (1 + (max hl hr)))[@K2 ])
  | K2 (k,hl) -> let x = arg  in k (1 + (max hl hr)) 
[%%print let x = () ]
