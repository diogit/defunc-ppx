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

(** 1. Gerar a Hash Table com informação de variáveis livres. *)

(* para guardar as variáveis livres: usar uma Hash Table que associa
   nomes (strings) dos [fun] a uma lista associativa. Exemplo:
   {
     K0 |-> [ ]
     K1 |-> [ (r, t); (k, int -> 'a) ]
     K2 |-> [ (k, int -> 'a); (hl, int) ]
   }
*)

(** 2. Gerar o tipo [kont], utilizando a informação gerada no passo anterior. *)

type kont =
  | K0
  | K1 of t * kont
  | K2 of kont * int

(** 3. Applicar a transformação de desfuncionalização à função [main] e às
    seguintes.
    3.1 Cada vez que ocorre um [fun] no programa original, este deve ser
        substituído pelo construtor algébrico com o mesmo nome. Se existem
        variávies livres no [fun] original, essas variáveis livres devem também
        ser usadas como argumentos do construtor algébrico. Por exemplo, no [K1]
        detectamos duas variáveis livres ([r] e [k]), portanto invocamos o [K1]
        da seguinte forma: [K1 (r, k)].
    3.2 Cada vez que ocorre uma aplicação da continuação [k], esta deve ser
        substituída por uma chamada à função [apply]. A função [apply] é gerada
        durante a desfuncionalização, como passamos a explicar.
    3.3 Gerar a função [apply]. A função [apply] recebe dois argumentos: [k] e
        [arg]. O corpo do [apply] é simplesmente um pattern-matching sobre os
        construtores do tipo [kont]. Para cada ramo deste pattern-matching,
        fazemos sempre o seguinte bidding: [| K1 -> let hl = arg in E], onde
        [hl] é o nome do argumento que estava associado ao [fun] de nome [K1] e
        onde [E] representa o corpo de [K1]. Nota importante: no corpo [E]
        também teremos de proceder à desfuncionalização. Isto é, substituir
        [fun] por construtor algébrico, ou substituir aplicações da continuação
        [k] por chamadas à função [apply]. *)

(** Nota: todas as funções, quer seja a [main] e a seguinte e mesmo a [apply]
          que se gere, devem ser mutuamente recursiva. *)

let rec main t =
  h_cps t K0

and h_cps t k =
  match t with
  | E -> apply k 0
  | N (l, r) ->
    h_cps l (K1 (r, k))

and apply (k: kont) arg =
  match k with
  | K0 -> let x = arg in x
  | K1 (r, k) -> let hl = arg in h_cps r (K2 (k, hl)) (* inlining do corpo do fun *)
  | K2 (k, hl) -> let hr = arg in apply k (1 + max hl hr)
