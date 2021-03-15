open Ast_mapper
open Ast_helper
open Asttypes
open Parsetree
open Longident

(* DEBUG *)
let rec p = function [] -> Format.printf "[]" | x::xs -> (Format.printf "%s;" x); p xs

type func = Func of string * string list * Parsetree.expression

let constructTuple l =
  let rec constructList l =
    match l with
    | [] -> []
    | x::xs -> (Exp.construct ({txt = Lident x; loc=(!default_loc)}) None) :: (constructList xs)
  in Exp.tuple (constructList l)

let isSingleArg args = if List.length args = 1 then true else false

let writeCacheArgs args =
  if isSingleArg args
  then Exp.ident {txt = Lident (List.hd args); loc=(!default_loc)}
  else Exp.ident {txt = Lident "arg"; loc=(!default_loc)}

let seq args = Exp.sequence
  (Exp.apply
    (Exp.ident ({ txt = Ldot (Lident "Hashtbl", "add"); loc=(!default_loc)}))
    [(Nolabel, Exp.ident {txt = Lident "cache"; loc=(!default_loc)});
     (Nolabel, writeCacheArgs args);
     (Nolabel, Exp.ident {txt = Lident "res"; loc=(!default_loc)})]
  )
  (Exp.ident {txt = Lident "res"; loc=(!default_loc)})

let letyBinding expression = Vb.mk (Pat.var {txt = "res"; loc=(!default_loc)}) (expression)

let matchRight expression args = Exp.let_ Nonrecursive [(letyBinding expression)] (seq args)  

let withCase expression args = 
  {
    pc_lhs = Pat.construct {txt = Lident "Not_found"; loc=(!default_loc)}
  None; 
  	pc_guard = None;
  	pc_rhs = (matchRight expression args)
  }

let cacheFind args = Exp.apply
  (Exp.ident ({ txt = Ldot (Lident "Hashtbl", "find"); loc=(!default_loc)}))
  [(Nolabel, Exp.ident {txt = Lident "cache"; loc=(!default_loc)});
   (Nolabel, writeCacheArgs args)]

let tryExp expression args = Exp.try_ (cacheFind args) [(withCase expression args)]

let rec gExp expression args =
  let keepArgs = args in
  let rec writeArgs = function
  | [] -> begin
            if isSingleArg args
            then tryExp expression keepArgs
            else Exp.let_ Nonrecursive [(Vb.mk (Pat.var {txt = "arg"; loc=(!default_loc)}) (constructTuple args))] (tryExp expression keepArgs)
          end
  | x::xs -> Exp.fun_ Nolabel None ((Pat.var {txt = x; loc=(!default_loc)})) (writeArgs xs)
  in writeArgs args

let g rec_flag funName expression args =
  Exp.let_
  rec_flag
  [Vb.mk (Pat.var {txt = funName; loc=(!default_loc)}) (gExp expression args)]
  (Exp.fun_ Nolabel None (Pat.var {txt = "x"; loc=(!default_loc)})
  (Exp.apply (Exp.ident {txt = Lident funName; loc=(!default_loc)}) [(Nolabel, Exp.ident {txt = Lident "x"; loc=(!default_loc)})]))
  (*(Exp.ident {txt = Lident funName; loc=(!default_loc)})*)

let cacheCreate = Vb.mk (Pat.var {txt = "cache"; loc=(!default_loc)})
  (Exp.apply
    (Exp.ident ({ txt = Ldot (Lident "Hashtbl", "create"); loc=(!default_loc)}))
    [(Nolabel, Exp.constant (Pconst_integer ("16", None)))]
  )

let memoExp rec_flag funName expression args = Exp.let_ Nonrecursive [cacheCreate] (g rec_flag funName expression args)

let fix_memo rec_flag funcList = 
  let rec writeFuncs funcList =
    match funcList with
    | [] -> []
    | Func(name, args, expr)::xs -> Vb.mk (Pat.var {txt = name; loc=(!default_loc)}) (memoExp rec_flag name expr args)::(writeFuncs xs)
  in Str.value
     (if List.length funcList > 1
     then Recursive
     else Nonrecursive)
     (writeFuncs funcList)

let rec getFuncArgsAndBody functionName args expr =
  match expr with
  | {pexp_desc = pexp;_} -> 
    begin
      match pexp with
      | Pexp_fun (Nolabel, None, {ppat_desc = Ppat_var {txt = arg;_};_}, body) -> getFuncArgsAndBody functionName (arg::args) body
      | _ -> if List.length args = 0
             then raise (Location.Error (Location.error ("The function "^functionName^" must have at least one argument!")))
             else Func(functionName, (List.rev args), expr)
    end

let rec createFunc functions =    
  match functions with
  | [] -> []
  | {pvb_pat = {ppat_desc = Ppat_var {txt = functionName;_};_}; pvb_expr = expression;_}::xs -> (getFuncArgsAndBody functionName [] expression)::(createFunc xs)
  | {pvb_pat = {ppat_desc = (Ppat_any | Ppat_alias (_, _) | Ppat_constant _| Ppat_interval (_, _) | Ppat_tuple _ | Ppat_construct (_, _) | Ppat_variant (_, _) | Ppat_record (_, _) | Ppat_array _| Ppat_or (_, _) | Ppat_constraint (_, _) | Ppat_type _ | Ppat_lazy _ | Ppat_unpack _ | Ppat_exception _ | Ppat_extension _ | Ppat_open (_, _)); _ }; _ }::_ -> raise (Location.Error (Location.error "Syntax error in expression mapper"))

let rec str_item_mapper mapper str = 
   begin match str with
      | { pstr_desc =
          Pstr_extension (({ txt = "memo"; loc }, pstr), _attributes); _} -> 
          begin 
            match pstr with
            | PStr [{ pstr_desc =
                    Pstr_value (rec_flag,
                    l); _}] -> fix_memo rec_flag (createFunc l)
            | PStr [{ pstr_desc =
                    Pstr_eval ({pexp_desc =
                      Pexp_let (rec_flag, l, exp); _}, _) ; _}] -> fix_memo rec_flag (createFunc l)
            | _ -> raise (Location.Error (Location.error ~loc "Syntax error in expression mapper"))                       
          end
      (* Delegate to the default mapper. *)
      | x -> default_mapper.structure_item mapper x;
      end

let memo_mapper _argv =
  { 
    default_mapper with
    structure_item = str_item_mapper
  }
 
let () = register "memo" memo_mapper
