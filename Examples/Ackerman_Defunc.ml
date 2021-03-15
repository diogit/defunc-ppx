let rec ackerman m n =
    match m, n with
      | 0, n -> n + 1
      | m, 0 -> ackerman (m - 1) 1
      | m, n -> ackerman (m - 1) (ackerman m (n - 1))

let rec ackermanANF m n =
    match m, n with
      | 0, n -> n + 1
      | m, 0 -> ackerman (m - 1) 1
      | m, n -> let m1 = ackerman m (n - 1) in
                let m2 = ackerman (m - 1) m1 in
                m2

let ackermanCPS m n =
    let rec ackerman m n k =
        match m, n with
        | 0, n -> k (n + 1)
        | m, 0 -> ackerman (m - 1) 1 k
        | m, n -> ackerman m (n - 1) (fun ack1 ->
                  ackerman (m - 1) ack1 (fun ack2 ->
                  k ack2))
    in ackerman m n (fun s -> s)

type kont = Kid
    | Lam1 of int * kont

let ackermanDefunc m n =
    let rec ackerman m n k =
        match m, n with
        | 0, n -> apply (n + 1) k
        | m, 0 -> ackerman (m - 1) 1 k
        | m, n -> ackerman m (n - 1) (Lam1 (m, k))
    and apply arg k =
        match k with
        | Kid -> arg
        | Lam1 (m, kont) -> ackerman (m - 1) arg kont
    in ackerman m n Kid

(*
ackermanDefunc 3 2 <-
ackerman 3 1 (Lam1 (2, Kid)) ->
ackerman 3 1 Lam1 (2, Kid) <-
ackerman 3 0 Lam1 (Lam1 (1, Lam1 (2, Kid))) ->
ackerman 3 0 Lam1 (Lam1 (1, Lam1 (2, Kid))) <-
ackerman 2 1 Lam1 (Lam1 (1, Lam1 (2, Kid))) ->
ackerman 2 1 Lam1 (Lam1 (1, Lam1 (2, Kid))) <-
ackerman 2 0 (Lam1 (1, Lam1 (Lam1 (1, Lam1 (2, Kid))))) ->
ackerman 2 0 (Lam1 (1, Lam1 (Lam1 (1, Lam1 (2, Kid))))) <-

*)