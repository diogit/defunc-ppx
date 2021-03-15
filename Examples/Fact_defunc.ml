let rec fact n = if n = 0 then 1 else n * fact (n - 1)

let rec factANF n = if n = 0
                    then 1 
                    else let fact = fact (n - 1) in
                         n * fact

let factCPS n =
    let rec fact n k =
        if n = 0
        then k 1
        else fact (n - 1) (fun s -> k (n * s))
    in fact n (fun s -> s)
;;

factCPS 10_000_000;;

type kont = Kid | Knext of int * kont

let rec fact_defunc n k =
    if n = 0
    then apply 1 k
    else fact_defunc (n - 1) (Knext(n, k))
    and apply arg = function
        | Kid -> let x = arg in x
        | Knext(i, k) -> let o = arg in apply (o * i) k