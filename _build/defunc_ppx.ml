open Ast_mapper
open Ast_helper
open Asttypes
open Parsetree
open Longident

let print_hashtbl k v = print_string ("("^k^"; "^v^") ")

let print_hashtbl2 k v =
  let rec printv v =
  match v with
  | [] -> ()
  | x::xs -> print_string (x^", "); printv xs
  in print_string ("("^k^"; [");
     printv v;
     print_string "])\n"
let print_queue q = 
  let print q =
      Queue.iter (fun e -> print_string (e^", ")) q
  in print_string "(";print q;print_string ") "
let free_vars = Hashtbl.create 16
let free_vars2 = Hashtbl.create 16
let vars = Hashtbl.create 16
let attributes = Queue.create ()
let current_attribute = Stack.create ()
let seen_funcs = Hashtbl.create 16

let get_attribute attributes =
  match attributes with
  | [] -> ""
  | (a, _)::_ -> a.txt

let get_expression_desc expr =
  match expr with
  | {
    pexp_desc = expression_desc;
    pexp_loc = _;
    pexp_attributes = pexp_attributes;
    } -> let attr = get_attribute pexp_attributes in
         (if String.length attr > 0
         then (Stack.push attr current_attribute;
              Queue.add attr attributes));
         expression_desc

let get_expression_desc_attribute expr =
  match expr with
  | {
    pexp_desc = _;
    pexp_loc = _;
    pexp_attributes = attributes;
    } -> get_attribute attributes

let get_pattern_desc patt =
  match patt with
  | {
  	ppat_desc = pattern_desc;
  	ppat_loc = _;
  	ppat_attributes = _;
    } -> pattern_desc

let add_var k v =
  (Hashtbl.add free_vars k v;
  print_string ("Just added: ("^k^", "^v^"), to the hashtbl.\n");
  try print_string ("Current attribute: "^Stack.top current_attribute^"\n")
  with | Stack.Empty -> ())

let rec get_type core_type_desc =
match core_type_desc with
|	Ptyp_any -> ""
|	Ptyp_var var -> var
|	Ptyp_arrow (arg_label, {ptyp_desc = core_type_desc1; _}, {ptyp_desc = core_type_desc2; _}) -> (get_type core_type_desc1)^" -> "^(get_type core_type_desc2)
|	Ptyp_tuple core_type_list -> ""
|	Ptyp_constr (loc, core_type_list) -> Longident.last loc.txt
|	Ptyp_object (_, closed_flag) -> ""
|	Ptyp_class (loc, core_type_list) -> ""
|	Ptyp_alias (core_type, string) -> ""
|	Ptyp_variant (row_field_list, closed_flag, label_list_option) -> ""
|	Ptyp_poly (loc_list, core_type) -> ""
|	Ptyp_package package_type -> ""
|	Ptyp_extension extension -> ""

let rec free_variables exp =
  match exp with
    | Pexp_ident {txt = Lident var; _} ->
      (try
        let key = Stack.top current_attribute in
        Stack.iter (fun key -> add_var (key^var) var) current_attribute;
        Stack.iter (fun key ->
          try let v1 = Hashtbl.find free_vars2 key in
            (* Hashtbl.remove free_vars2 key;
            Hashtbl.add free_vars2 key (v1@[var]) *)
            Hashtbl.replace free_vars2 key (v1@[var])
          with | Not_found -> Hashtbl.add free_vars2 key [var])
          current_attribute;
        (*)
        add_var (key^var) var
        *)
      with | Stack.Empty -> ());
      print_string ("Pexp_ident "^var^"\n");
      Hashtbl.add seen_funcs var var;
      print_string "Seen functions: ";
      Hashtbl.iter print_hashtbl seen_funcs;
      (*)
      print_string "Current Hashtbl: ";
      Hashtbl.iter print_hashtbl free_vars; *)
      print_string "\n";
    | Pexp_fun (_, _, {ppat_desc = Ppat_var {txt = var; _}; _}, {pexp_desc = e; _}) ->
      free_variables e;
      (try
        (*)
        Hashtbl.remove free_vars (key^var);
        *)
        Stack.iter (fun key -> Hashtbl.remove free_vars (key^var)) current_attribute;
        Stack.iter (fun key ->
          try let v1 = Hashtbl.find free_vars2 key in
            (* Hashtbl.remove free_vars2 key;
            Hashtbl.add free_vars2 key (List.rev (List.tl (List.rev v1))) *)
            Hashtbl.replace free_vars2 key (List.rev (List.tl (List.rev v1)))
          with | Not_found -> Hashtbl.add free_vars2 key [var])
          current_attribute;
        let key = Stack.pop current_attribute in
        print_string ("Just removed: ("^key^", "^var^"), from the hashtbl.\n");
        print_string ("Pexp_fun + Ppat_var, removed: "^(Stack.top current_attribute)^"\n")
      with | Stack.Empty -> print_string ("Empty Stack ( , "^var^")\n"));
    | Pexp_fun (_, _, {ppat_desc = Ppat_constraint ({ppat_desc = Ppat_var {txt = var; _}; _},
      {ptyp_desc = core_type_desc; _}); _},
      {pexp_desc = e; _}) ->
      Hashtbl.add vars (var) (get_type core_type_desc);
      print_string ("Type: "^var^": "^(get_type core_type_desc)^"\n");
      free_variables e;
      (try
                (*)
        Hashtbl.remove free_vars (key^var);
        *)
        Stack.iter (fun key -> Hashtbl.remove free_vars (key^var)) current_attribute;
        Stack.iter (fun key ->
          try let v1 = Hashtbl.find free_vars2 key in
            (* Hashtbl.remove free_vars2 key;
            Hashtbl.add free_vars2 key (List.rev (List.tl (List.rev v1))) *)
            Hashtbl.replace free_vars2 key (List.rev (List.tl (List.rev v1)))
          with | Not_found -> Hashtbl.add free_vars2 key [var])
          current_attribute;
        let key = Stack.pop current_attribute in
        print_string ("Just removed: ("^key^", "^var^"), from the hashtbl.\n");
        print_string ("Pexp_fun + Ppat_constraint, removed: "^(Stack.top current_attribute)^"\n")
      with | Stack.Empty -> print_string ("Empty Stack ( , "^var^")\n"));
    |	Pexp_constant _ -> ()
    |	Pexp_let (_, value_binding_list , expression) ->
      List.iter free_vars_value_binding value_binding_list;
      free_variables (get_expression_desc expression)
    |	Pexp_function case_list -> List.iter free_vars_case case_list
    (*)
    |	Pexp_apply (expression1, expression_list) -> 
      free_variables (get_expression_desc expression1);
      List.iter (fun (_, y) -> free_variables (get_expression_desc y)) expression_list;*)
    |	Pexp_apply ({pexp_desc = Pexp_ident {txt = Lident var; _}; _}, expression_list) ->
      if var = "k"
      then free_variables (Pexp_ident {txt = Lident var; loc = Location.none});
      List.iter (fun (_, y) -> free_variables (get_expression_desc y)) expression_list
    |	Pexp_match (expression , case_list) ->
      free_variables  (get_expression_desc expression);
      List.iter free_vars_case case_list
    |	Pexp_try (expression , case_list) -> 
      free_variables  (get_expression_desc expression);
      List.iter free_vars_case case_list
    |	Pexp_tuple (expression_list) -> 
      List.iter (fun x -> free_variables  (get_expression_desc x)) expression_list
    |	Pexp_construct (_, expression_option) ->
      begin
      match expression_option with
      | Some expr -> free_variables  (get_expression_desc expr)
      | None -> ()
      end
    |	Pexp_variant (_, expression_option) ->
      begin
      match expression_option with
      | Some expr -> free_variables  (get_expression_desc expr)
      | None -> ()
      end
    |	Pexp_record (expression_list, expression_option) -> 
      List.iter (fun (_, y) -> free_variables  (get_expression_desc y)) expression_list;
      begin
      match expression_option with
      | Some expr -> free_variables  (get_expression_desc expr)
      | None -> ()
      end
    |	Pexp_field (expression , _) -> free_variables  (get_expression_desc expression)
    |	Pexp_setfield (expression1, _, expression2) ->
      free_variables  (get_expression_desc expression1);
      free_variables  (get_expression_desc expression2)
    |	Pexp_array (expression_list) -> 
      List.iter (fun x -> free_variables  (get_expression_desc x)) expression_list
    |	Pexp_ifthenelse (expression1, expression2, expression_option) ->
      free_variables  (get_expression_desc expression1);
      free_variables  (get_expression_desc expression2);
      begin
      match expression_option with
      | Some expr -> free_variables  (get_expression_desc expr)
      | None -> ()
      end
    |	Pexp_sequence (expression1, expression2) ->
      free_variables  (get_expression_desc expression1);
      free_variables  (get_expression_desc expression2)
    |	Pexp_while (expression1, expression2) -> 
      free_variables  (get_expression_desc expression1);
      free_variables  (get_expression_desc expression2)
    |	Pexp_for (pattern, expression1, expression2, _, expression) ->
      free_variables  (get_expression_desc expression1);
      free_variables  (get_expression_desc expression2);
      free_variables  (get_expression_desc expression);
    |	Pexp_constraint (expression, _) -> free_variables  (get_expression_desc expression)
    |	Pexp_coerce (expression, _, _) -> free_variables  (get_expression_desc expression)
    |	Pexp_send (expression, _) -> free_variables  (get_expression_desc expression)
    |	Pexp_new _ -> ()
    |	Pexp_setinstvar (_, expression) -> free_variables  (get_expression_desc expression)
    |	Pexp_override expression_list -> List.iter (fun (_, y) -> free_variables  (get_expression_desc y)) expression_list;
    |	Pexp_letmodule (_, _, expression) -> free_variables  (get_expression_desc expression)
    |	Pexp_letexception (_, expression) -> free_variables  (get_expression_desc expression)
    |	Pexp_assert expression -> free_variables  (get_expression_desc expression)
    |	Pexp_lazy expression -> free_variables  (get_expression_desc expression)
    |	Pexp_poly (expression, _) -> free_variables  (get_expression_desc expression)
    |	Pexp_object _ -> ()
    |	Pexp_newtype (_ , expression) -> free_variables  (get_expression_desc expression)
    |	Pexp_pack _ -> ()
    |	Pexp_open (_, _, expression) -> free_variables  (get_expression_desc expression)
    |	Pexp_extension extension -> ()
    |	Pexp_unreachable -> ()
    | _ -> print_string "something wasn't caught"
    ;
    let _ = Str.type_ Recursive
      [Type.mk {txt = "kont"; loc=(!default_loc)}] 
    in ()
and free_vars_value_binding vb =
  match vb with
  | {
  	pvb_pat = pattern;
  	pvb_expr = expression;
  	pvb_attributes = attributes;
  	pvb_loc = t;
    } -> free_variables (get_expression_desc expression)
and free_vars_case case =
  match case with
  | {
  	pc_lhs = pattern;
  	pc_guard = expression_option;
  	pc_rhs = expression;
    } ->
      free_vars_pattern_desc (get_pattern_desc pattern);
      begin
      match expression_option with
      | Some exp -> free_variables (get_expression_desc exp)
      | None -> ()
      end;
      free_variables (get_expression_desc expression)
and free_vars_pattern_desc patt_desc =
  match patt_desc with
  |	Ppat_any -> ()
  |	Ppat_var _-> ()
  |	Ppat_alias (pattern, _) -> free_vars_pattern_desc (get_pattern_desc pattern)
  |	Ppat_constant _ -> ()
  |	Ppat_interval _ -> ()
  |	Ppat_tuple pattern_list -> List.iter (fun x -> free_vars_pattern_desc (get_pattern_desc x)) pattern_list
  |	Ppat_construct (_, pattern_option) ->
    begin
      match pattern_option with
      | Some pattern -> free_vars_pattern_desc (get_pattern_desc pattern)
      | None -> ()
    end
  |	Ppat_variant (_, pattern_option) -> 
    begin
      match pattern_option with
      | Some pattern -> free_vars_pattern_desc (get_pattern_desc pattern)
      | None -> ()
    end
  |	Ppat_record (pattern_list, _) -> List.iter (fun (_, y) -> free_vars_pattern_desc  (get_pattern_desc y)) pattern_list;
  |	Ppat_array pattern_list -> List.iter (fun x -> free_vars_pattern_desc (get_pattern_desc x)) pattern_list
  |	Ppat_or (pattern1, pattern2) -> free_vars_pattern_desc (get_pattern_desc pattern1);
                                    free_vars_pattern_desc (get_pattern_desc pattern2)
  (*)
  |	Ppat_constraint (pattern, _) -> free_vars_pattern_desc (get_pattern_desc pattern)
  *)
  | Ppat_constraint ({ppat_desc = Ppat_var {txt = var; _}; _}, {ptyp_desc = core_type_desc; _}) -> 
      Hashtbl.add vars (var) (get_type core_type_desc);
      print_string ("Type: "^var^": "^(get_type core_type_desc)^"\n")
  |	Ppat_type _ -> ()
  |	Ppat_lazy pattern -> free_vars_pattern_desc (get_pattern_desc pattern)
  |	Ppat_unpack _ -> ()
  |	Ppat_exception pattern -> free_vars_pattern_desc (get_pattern_desc pattern)
  |	Ppat_extension (_, payload) -> free_vars_payload payload
  |	Ppat_open (_, pattern) -> free_vars_pattern_desc (get_pattern_desc pattern)
  | _ -> ()
and free_vars_payload payload =
  match payload with
  |	PStr structure -> ()
  |	PSig signature -> ()
  |	PTyp core_type -> ()
  |	PPat (pattern, expression_option) -> ()

let print_attributes attributes =
if List.length attributes > 0 then
match List.hd attributes with
| (a, _) -> 
if List.length attributes > 0 then (Format.printf "attribute found: %s;" a.txt)
else (Format.printf "%s;" "no attributes found")
else (Format.printf "%s;" "no attributes found")

let get_fun_expression expression_desc =
 match expression_desc with
 | Pexp_fun (arg_label, expression_option, pattern, expression) -> expression
let get_fun_expression_desc expr =
  match expr with
  | {
    pexp_desc = expression_desc;
    pexp_loc = location;
    pexp_attributes = attributes;
    } -> expression_desc

let get_attributes expr =
  match expr with
  | {
    pexp_desc = expression_desc;
    pexp_loc = location;
    pexp_attributes = attributes;
    } -> attributes

let get_value_binding_expression value_binding =
match value_binding with
| {
  pvb_pat = pattern;
  pvb_expr = expression;
  pvb_attributes = attributes;
  pvb_loc = location;
  } -> expression

let rec iterate_value_binding_list value_binding_list  =
  match value_binding_list with
  | x::xs -> x 

let get_value_binding structure_item_desc =
  match structure_item_desc with
  | Pstr_eval (expression , attributes) -> []
  | Pstr_value (rec_flag , value_binding_list) -> value_binding_list
  | Pstr_primitive value_description -> []
  | Pstr_type (rec_flag , type_declaration_list) -> []
  | Pstr_typext type_extension -> []
  | Pstr_exception type_exception -> []
  | Pstr_module module_binding -> []
  | Pstr_recmodule module_binding_list -> []
  | Pstr_modtype module_type_declaration -> []
  | Pstr_open open_declaration -> []
  | Pstr_class class_declaration_list -> []
  | Pstr_class_type class_type_declaration_list -> []
  | Pstr_include include_declaration -> []
  | Pstr_attribute attribute -> []
  | Pstr_extension (extension , attributes) -> []

let rec build_type_aux vars_list =
  match vars_list with
  | [] -> [] 
  | x::xs ->
    let var_type = if x = "k" then "kont" else Hashtbl.find vars x in
  Typ.mk (Ptyp_constr ({txt = Lident var_type; loc=(!default_loc)}, [])) :: build_type_aux xs

let rec build_type s =
  try
    let e = Stack.pop s in
    Type.constructor {txt = fst e; loc=(!default_loc)}
    ~args:(Pcstr_tuple (build_type_aux (snd e)))
    :: build_type s
  with | Stack.Empty -> []

let rec case_match_vars vars_tuple =
  match vars_tuple with
  | [] -> []
  | x::xs -> Pat.var {txt = x; loc=(!default_loc)} :: case_match_vars xs

let rec e4 s =
  try
    let e = Stack.pop s in
    let vars = snd e in
    Exp.case (Pat.construct {txt = Lident (fst e); loc=(!default_loc)}
      (if List.length vars > 0
      then Some (Pat.tuple (case_match_vars vars))
      else None))
      (Exp.let_
        Nonrecursive
        [Vb.mk (Pat.var {txt = "x"; loc=(!default_loc)}) (Exp.ident {txt = Lident "arg"; loc=(!default_loc)})]
        (Exp.ident {txt = Lident "x"; loc=(!default_loc)}))
    :: e4 s
  with | Stack.Empty -> []

(*
and apply (k: kont) arg =
  match k with
  | K0 -> let x = arg in x
  | K1 (r, k) -> let hl = arg in h_cps r (K2 (k, hl)) (* inlining do corpo do fun *)
  | K2 (k, hl) -> let hr = arg in apply k (1 + max hl hr)
   *)

let e3 =
  let write = Stack.create () in
  Hashtbl.iter (fun k v -> Stack.push (k, v) write) free_vars2;
  print_string ("\nfree_vars2 length: "^string_of_int (Hashtbl.length free_vars2)^"\n");
  Exp.match_ (Exp.ident {txt = Lident "k"; loc=(!default_loc)}) (e4 write)

let e2 = Exp.fun_ Nolabel None (Pat.var {txt = "arg"; loc=(!default_loc)}) e3

let e1 = Exp.fun_ Nolabel None (Pat.constraint_ (Pat.var {txt = "k"; loc=(!default_loc)}) (Typ.mk (Ptyp_constr ({txt = Lident "kont"; loc=(!default_loc)}, [])))) e2

let apply = Vb.mk (Pat.var {txt = "apply"; loc=(!default_loc)}) e1

let rec transform_defunc rec_flag vb_list =
  Str.value rec_flag [apply]

let rec str_item_defunc_mapper mapper str = 
   begin match str with
      | { pstr_desc =
          Pstr_extension (({ txt = "defun"; loc }, pstr), _attributes); _} -> 
          begin 
            match pstr with
            | PStr [{ pstr_desc =
                    Pstr_value (rec_flag,
                    l); _}] ->
                      let act1 = List.iter free_vars_value_binding l in
                      let act2 =
                      let write = Stack.create () in
                        Hashtbl.iter (fun k v -> Stack.push (k, v) write) free_vars2;
                        Str.type_ Recursive [
                          Type.mk {txt = "kont"; loc=(!default_loc)}
                          ~kind:(Ptype_variant (build_type write))]
                      in
                      let act3 = transform_defunc rec_flag l in
                      act1; act2; act3
            | PStr [{ pstr_desc =
                    Pstr_eval ({pexp_desc =
                      Pexp_let (rec_flag, l, exp); _}, _) ; _}] -> Str.value rec_flag l
            | _ -> raise (Location.Error (Location.error ~loc "Syntax error in expression mapper"))                       
          end
      (* Delegate to the default mapper. *)
      | x -> default_mapper.structure_item mapper x;
      end

let rec str_item_print_mapper mapper str = 
   begin match str with
      | { pstr_desc =
          Pstr_extension (({ txt = "print"; _ }, _), _); _} ->
          print_string "%print found \n";
          print_string "Free vars: ";
          Hashtbl.iter print_hashtbl free_vars;
          print_string "\nFree vars2: ";
          Hashtbl.iter print_hashtbl2 free_vars2;
          print_string "\nVars: ";
          Hashtbl.iter print_hashtbl vars;
          print_string "\nAttributes: ";
          print_queue attributes;
          Str.eval (Exp.constant (Pconst_string ("", None)));

            (* [
              Type.constructor {txt = k1; loc=(!default_loc)};
              Type.constructor {txt = k2; loc=(!default_loc)}
              ~args:(Pcstr_tuple [Typ.mk (Ptyp_constr ({txt = Lident (Hashtbl.find vars (Hashtbl.find free_vars "K1r")); loc=(!default_loc)}, []));
                                  Typ.mk (Ptyp_constr ({txt = Lident (Hashtbl.find vars (Hashtbl.find free_vars "K1k")); loc=(!default_loc)}, []))]);
              Type.constructor {txt = k3; loc=(!default_loc)}
              ~args:(Pcstr_tuple [Typ.mk (Ptyp_constr ({txt = Lident (Hashtbl.find vars (Hashtbl.find free_vars "K2k")); loc=(!default_loc)}, []));
                                  Typ.mk (Ptyp_constr ({txt = Lident (Hashtbl.find vars (Hashtbl.find free_vars "K2hl")); loc=(!default_loc)}, []))])
            ] *)
      (* Delegate to the default mapper. *)
      | x -> default_mapper.structure_item mapper x;
      end

let defunc_mapper _argv =
  { 
    default_mapper with
    structure_item = str_item_defunc_mapper
  }

let print_mapper _argv =
  { 
    default_mapper with
    structure_item = str_item_print_mapper
  }

let () = register "defun" defunc_mapper;
         (* register "print" print_mapper *)