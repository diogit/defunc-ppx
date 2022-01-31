type t = E | N of t * t

let rec main t =
  h_cps t (fun [@K0] x -> x) (* FV : K0 |-> { } *)

and h_cps (t: t) (k: int -> 'a) =
  match t with
  | E -> k 0
  | N ((l: t), (r: t)) ->
    h_cps l (fun [@K1] (hl: int) -> (* FV: K1 |-> { r: t; k: int -> 'a } *)
    h_cps r (fun [@K2] (hr: int) -> (* FV: K2 |-> { k: int -> 'a; hl: int } *)
            k (1 + max hl hr)))

let build_tree =
  let cache = Hashtbl.create 15  in
  let rec create_tree h =
    try Hashtbl.find cache h
    with
    | Not_found  ->
        let y = if h = 0 then E else N (E, create_tree (h - 1))  in
        (Hashtbl.add cache h y; y)
     in
  create_tree

let rec height t =
  match t with
  | E -> 0
  | N (l, r) -> 1 + max (height l) (height r)

open Format

module Time = struct

  open Unix

  let utime f x =
    let u = (times()).tms_utime in
    let z = f x in
    let ut = (times()).tms_utime -. u in
    (z,ut)

  let print f x y =
    let (y,ut) = utime f x in
    printf "user time: %2.2f@." ut;
    y

end

let () =
  let tree = build_tree 1_000_000 in
  (* Format.eprintf "@[%a@]@." Tree.pp_tree t1; *)
  Gc.print_stat stderr;
  print_float (Gc.allocated_bytes ());
  (* let b, t = Time.utime (fun x -> x) HTree.create_tree 100_000 in
  eprintf "t1 create t2? (%f s)@." t; *)
  (* let b, t = Time.utime (height) tree in
  eprintf "t1 height t2? (%f s)@." t; *)
  let b, t = Time.utime (main) tree in
  eprintf "t1 defunc height t2? (%f s)@." t
