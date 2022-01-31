
type t = E | N of t * t

(* CPS *)

let rec height t k = match t with
  | E -> k 0
  | N (t1, t2) -> height t1 (fun o1 ->
                  height t2 (fun o2 -> k (1 + max o1 o2)))

(* Defuncionalization *)

type kont =
  | Kid
  | Kleft of t * kont
  | Kright of int * kont

let rec height_def t k = match t with
  | E -> apply k 0
  | N (t1, t2) -> height_def t1 (Kleft (t2, k))
  
and apply k arg = match k with
  | Kid -> arg 
  | Kleft (t2, k) -> let o1 = arg in height_def t2 (Kright (o1, k))
  | Kright (o1, k) -> let o2 = arg in apply k (1 + max o1 o2)


(* Criar árvore *)

let rec leftist_tree t = function
  | 0 -> t
  | n -> leftist_tree (N (t, E)) (n - 1)

(* Variaveis a usar *)
let t1 = leftist_tree E 1_000_000

let () = 
  let open Format in
    eprintf "height_CPS(t1): %d@." (height t1 (fun x -> x));
    eprintf "height_Def(t1): %d@." (height_def t1 Kid)
  ;;
