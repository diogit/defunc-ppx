let rec fib n = if n <= 1 then 1 else fib (n - 2) + fib (n - 1)

let rec fibANF n =
    if n <= 1
    then 1
    else let fib1 = fib (n - 2) in
    let fib2 = fib (n - 1) in
    fib1 + fib2

let fibCPS n =
    let rec fib n k =
        if n <= 1
        then k 1
        else fib (n - 2) (fun k1 ->
        fib (n - 1) (fun k2 ->
        k (k1 + k2))) in
    fib n (fun s -> s)

type kont = Kid
    | Lam1 of int * kont
    | Lam2 of int * kont

let rec fibDefunc n k =
    if n <= 1
    then apply 1 k
    else fibDefunc (n - 2) (Lam1 (n, k))
    and apply arg k =
        match k with
        | Kid -> arg
        | Lam1 (n, kont) -> fibDefunc (n - 1) (Lam2(arg, kont))
        | Lam2 (n, kont) -> apply (arg + n) kont
