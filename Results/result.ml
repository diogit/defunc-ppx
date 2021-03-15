
free_vars2 length: 0
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
let rec apply (k : kont) arg = match k with 
[%%print let x = () ]
