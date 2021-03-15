let rec lucas n b1 b2 =
    match n with
    | 0 -> b1
    | 1 -> b2
    | n -> lucas (n - 1) b1 b2 + lucas (n - 2) b1 b2

let rec lucasANF n b1 b2 =
    match n with
    | 0 -> b1
    | 1 -> b2
    | n -> let l1 = lucas (n - 1) b1 b2 in
           let l2 = lucas (n - 2) b1 b2 in
           l1 + l2

let lucasCPS n b1 b2 =
    let rec lucas n b1 b2 k =
    match n with
    | 0 -> k b1
    | 1 -> k b2
    | n -> lucas (n - 1) b1 b2 (fun k1 ->
           lucas (n - 2) b1 b2 (fun k2 ->
           k (k1 + k2)))
    in lucas n b1 b2 (fun s -> s)

type kont = Kid
    | Lam1 of int * kont
    | Lam2 of int * kont

let lucasDefunc n b1 b2 =
    let rec lucas n b1 b2 k =
    match n with
    | 0 -> apply b1 k
    | 1 -> apply b2 k
    | n -> lucas (n - 1) b1 b2 (Lam1 (n, k))
    and apply arg k =
        match k with
        | Kid -> arg
        | Lam1 (n, kont) -> lucas (n - 2) b1 b2 (Lam2 (arg, kont))
        | Lam2 (n, kont) -> apply (arg + n) kont
    in lucas n b1 b2 Kid