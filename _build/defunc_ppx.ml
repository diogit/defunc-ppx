open Ast_mapper
open Ast_helper
open Asttypes
open Parsetree
open Longident

(* Debug Functions *)
let print_hashtbl k v = print_string ("("^k^"; "^v^") ")

let print_hashtbl_list k v =
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

(* Global Variables *)
(* Hashtbl to store attributes and free variables - (attribute, [variable]) *)
let free_vars = Hashtbl.create 16
(* Hashtbl to store free variables and types - (variable, type) *)
let vars = Hashtbl.create 16
(* Hashtbl to store attributes and function bodies - (attribute, function body) *)
let attr_bodies = Hashtbl.create 16
(* Hashtbl to store attributes and function args - (attribute, function arg) *)
let attr_args = Hashtbl.create 16
(* Queue to store attributes *)
let attributes = Queue.create ()
(* Stack to store current attributes *)
let current_attributes = Stack.create ()

(* Auxiliary functions *)
let get_attribute attributes =
  match attributes with
  | [] -> ""
  | (a, _)::_ -> a.txt
let getBody pexp_desc =
  match pexp_desc with
  | Pexp_fun (_, _, _, e) -> e
let getArg pexp_desc =
  match pexp_desc with
  | Pexp_fun (_, _, e, _) -> e
let get_expression_desc expr =
  match expr with
  | {
    pexp_desc = expression_desc;
    pexp_loc = _;
    pexp_attributes = pexp_attributes;
    } -> let attr = get_attribute pexp_attributes in
         (if String.length attr > 0
         then (Stack.push attr current_attributes;
              Queue.add attr attributes;
              Hashtbl.add attr_bodies attr (getBody expression_desc);
              Hashtbl.add attr_args attr (getArg expression_desc)));
         expression_desc
(* Applies a function to the value of an option *)
let f_option f opt =
  match opt with
  | None -> None
  | Some o -> Some (f o)

let get_pattern_desc patt =
  match patt with
  | {
  	ppat_desc = pattern_desc;
  	ppat_loc = _;
  	ppat_attributes = _;
    } -> pattern_desc

let rec get_type core_type_desc =
match core_type_desc with
|	Ptyp_any -> ""
|	Ptyp_var var -> var
|	Ptyp_arrow (_, {ptyp_desc = core_type_desc1; _}, {ptyp_desc = core_type_desc2; _}) -> (get_type core_type_desc1)^" -> "^(get_type core_type_desc2)
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
        Stack.iter (fun key ->
          try let v1 = Hashtbl.find free_vars key in
            Hashtbl.replace free_vars key (v1@[var])
          with | Not_found -> Hashtbl.add free_vars key [var])
          current_attributes;
      with | Stack.Empty -> ());
    | Pexp_fun (_, _, {ppat_desc = Ppat_var {txt = var; _}; _}, {pexp_desc = e; _}) ->
      free_variables e;
      (try
        Stack.iter (fun key ->
          try let v1 = Hashtbl.find free_vars key in
            Hashtbl.replace free_vars key (List.rev (List.tl (List.rev v1)))
          with | Not_found -> Hashtbl.add free_vars key [var])
          current_attributes;
        ignore(Stack.pop current_attributes)
      with | Stack.Empty -> ())
    | Pexp_fun (_, _, {ppat_desc = Ppat_constraint ({ppat_desc = Ppat_var {txt = var; _}; _},
      {ptyp_desc = core_type_desc; _}); _},
      {pexp_desc = e; _}) ->
      Hashtbl.add vars (var) (get_type core_type_desc);
      (* print_string ("Type: "^var^": "^(get_type core_type_desc)^"\n"); *)
      free_variables e;
      (try
        Stack.iter (fun key ->
          try let v1 = Hashtbl.find free_vars key in
            Hashtbl.replace free_vars key (List.rev (List.tl (List.rev v1)))
          with | Not_found -> Hashtbl.add free_vars key [var])
          current_attributes;
        ignore(Stack.pop current_attributes)
      with | Stack.Empty -> ())
    |	Pexp_constant _ -> ()
    |	Pexp_let (_, value_binding_list , expression) ->
      List.iter free_vars_value_binding value_binding_list;
      free_variables (get_expression_desc expression)
    |	Pexp_function case_list -> List.iter free_vars_case case_list
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
  | Ppat_constraint ({ppat_desc = Ppat_var {txt = var; _}; _}, {ptyp_desc = core_type_desc; _}) -> 
      Hashtbl.add vars (var) (get_type core_type_desc);
      (* print_string ("Type: "^var^": "^(get_type core_type_desc)^"\n") *)
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

(* Defunc starts here *)
let rec write_tuple var_list =
  match var_list with
  | [] -> []
  | x::xs -> Exp.ident ({txt = Lident x; loc=(!default_loc)}) :: write_tuple xs

(* Write the Apply function *)
let write_new_body v =
  let attr = Queue.take attributes in
  let free_vars = Hashtbl.find free_vars attr in
  Exp.construct ~attrs:[] {txt = Lident attr; loc=(!default_loc)}
  (if List.length free_vars > 0
   then Some (Exp.tuple (write_tuple free_vars))
   else None)

let rec defunc_expression_desc expression_desc =
  match expression_desc with
    | Pexp_ident t -> Pexp_ident t
    |	Pexp_constant constant -> Pexp_constant constant
    |	Pexp_let (rec_flag, value_binding_list, expression) -> Pexp_let (rec_flag, (List.map defunc_vb value_binding_list), defunc_expression expression)
    |	Pexp_function case_list -> Pexp_function (List.map defunc_case case_list)
    | Pexp_fun (arg_label, expression_option, pattern, expression) ->
      Pexp_fun (arg_label, expression_option, defunc_pattern pattern, defunc_expression expression)
    |	Pexp_apply ({pexp_desc = Pexp_ident {txt = Lident var; _}; _}, arg_label_expression_list) ->
      if var = "k"
      then
      Pexp_apply (
        (Exp.ident {txt = Lident "apply"; loc=(!default_loc)}),
        List.map (fun (arg_label, expression) -> (arg_label, defunc_expression expression))
        ((Nolabel, Exp.ident {txt = Lident var; loc=(!default_loc)})::arg_label_expression_list))
      else
      Pexp_apply (
        defunc_expression (Exp.ident {txt = Lident var; loc=(!default_loc)}),
        List.map (fun (arg_label, expression) -> (arg_label, defunc_expression expression)) arg_label_expression_list)
    |	Pexp_apply (expression, arg_label_expression_list) -> Pexp_apply (defunc_expression expression, List.map (fun (arg_label, expression) -> (arg_label, defunc_expression expression)) arg_label_expression_list)
    |	Pexp_match (expression, case_list) -> Pexp_match (defunc_expression expression, List.map defunc_case case_list)
    |	Pexp_try (expression , case_list) -> Pexp_try (defunc_expression expression, List.map defunc_case case_list)
    |	Pexp_tuple (expression_list) -> Pexp_tuple (List.map defunc_expression expression_list)
    |	Pexp_construct (t, expression_option) -> Pexp_construct (t, expression_option)
    |	Pexp_variant (label, expression_option) -> Pexp_variant (label, expression_option)
    |	Pexp_record (expression_list, expression_option) -> Pexp_record (expression_list, expression_option)
    |	Pexp_field (expression, t) -> Pexp_field (defunc_expression expression, t)
    |	Pexp_setfield (expression1, t, expression2) -> Pexp_setfield (defunc_expression expression1, t, defunc_expression expression2)
    |	Pexp_array (expression_list) -> Pexp_array (List.map defunc_expression expression_list)
    |	Pexp_ifthenelse (expression1, expression2, expression_option) -> Pexp_ifthenelse (defunc_expression expression1, defunc_expression expression2, expression_option)
    |	Pexp_sequence (expression1, expression2) -> Pexp_sequence (defunc_expression expression1, defunc_expression expression2)
    |	Pexp_while (expression1, expression2) -> Pexp_while (defunc_expression expression1, defunc_expression expression2)
    |	Pexp_for (pattern, expression1, expression2, direction_flag, expression) -> Pexp_for (defunc_pattern pattern, defunc_expression expression1, defunc_expression expression2, direction_flag, defunc_expression expression)
    |	Pexp_constraint (expression, core_type) -> Pexp_constraint (defunc_expression expression, defunc_core_type core_type)
    |	Pexp_coerce (expression, core_type_option, core_type) -> Pexp_coerce (defunc_expression expression, core_type_option, defunc_core_type core_type)
    |	Pexp_send (expression, loc) -> Pexp_send (defunc_expression expression, loc)
    |	Pexp_new t -> Pexp_new t
    |	Pexp_setinstvar (loc, expression) -> Pexp_setinstvar (loc, defunc_expression expression)
    |	Pexp_override list -> Pexp_override list
    |	Pexp_letmodule (loc, module_expr, expression) -> Pexp_letmodule (loc, defunc_module_expression module_expr, defunc_expression expression)
    |	Pexp_letexception (extension_constructor, expression) -> Pexp_letexception (extension_constructor, defunc_expression expression)
    |	Pexp_assert expression -> Pexp_assert (defunc_expression expression)
    |	Pexp_lazy expression -> Pexp_lazy (defunc_expression expression)
    |	Pexp_poly (expression, core_type_option) -> Pexp_poly (defunc_expression expression, core_type_option)
    |	Pexp_object class_structure -> Pexp_object class_structure
    |	Pexp_newtype (loc, expression) -> Pexp_newtype (loc, defunc_expression expression)
    |	Pexp_pack module_expr -> Pexp_pack (defunc_module_expression module_expr)
    |	Pexp_open (override_flag, t, expression) -> Pexp_open (override_flag, t, defunc_expression expression)
    |	Pexp_extension extension -> Pexp_extension extension
    |	Pexp_unreachable -> Pexp_unreachable
and defunc_expression expression =
         (* print_string ("Queue length: "^string_of_int (Queue.length attributes)^"\n"); *)
  match expression with
  | {
  	pexp_desc = expression_desc;
  	pexp_loc = t;
  	pexp_attributes = attributes;
    } -> let attr = get_attribute attributes in
         (* print_string ("Attribute: "^attr^"\n"); *)
         if String.length attr > 0
         then write_new_body None
         else
          {
            pexp_desc = defunc_expression_desc expression_desc;
            pexp_loc = t;
            pexp_attributes = attributes;
          }
and defunc_pattern pattern =
  match pattern with
  | {
  	ppat_desc = pattern_desc;
  	ppat_loc = t;
  	ppat_attributes = attributes;
    } -> {
          ppat_desc = defunc_pattern_desc pattern_desc;
          ppat_loc = t;
          ppat_attributes = attributes;
        }
and defunc_pattern_desc pattern_desc =
  match pattern_desc with
  |	Ppat_any -> Ppat_any
  |	Ppat_var loc -> Ppat_var loc
  |	Ppat_alias (pattern, loc) -> Ppat_alias (defunc_pattern pattern, loc)
  |	Ppat_constant constant -> Ppat_constant constant
  |	Ppat_interval (constant1, constant2) -> Ppat_interval (constant1, constant2)
  |	Ppat_tuple pattern_list -> Ppat_tuple (List.map defunc_pattern pattern_list)
  |	Ppat_construct (t, pattern_option) -> Ppat_construct (t, pattern_option)
  |	Ppat_variant (label, pattern_option) -> Ppat_variant (label, pattern_option)
  |	Ppat_record (list, closed_flag) -> Ppat_record (list, closed_flag)
  |	Ppat_array pattern_list -> Ppat_array (List.map defunc_pattern pattern_list)
  |	Ppat_or (pattern1, pattern2) -> Ppat_or (defunc_pattern pattern1, defunc_pattern pattern2)
  (* |	Ppat_constraint (pattern, core_type) -> Ppat_constraint (defunc_pattern pattern, defunc_core_type core_type) *)
  |	Ppat_constraint (pattern, _) -> 
    (* print_string "I was here \n"; *)
    get_pattern_desc (defunc_pattern pattern)
  |	Ppat_type t -> Ppat_type t
  |	Ppat_lazy pattern -> Ppat_lazy (defunc_pattern pattern)
  |	Ppat_unpack loc -> Ppat_unpack loc
  |	Ppat_exception pattern -> Ppat_exception (defunc_pattern pattern)
  |	Ppat_extension extension -> Ppat_extension extension
  |	Ppat_open (t, pattern) -> Ppat_open (t, defunc_pattern pattern)
and defunc_vb vb =
  match vb with
  | {
  	pvb_pat = pattern;
  	pvb_expr = expression;
  	pvb_attributes = attributes;
  	pvb_loc = t;
    } -> {
          pvb_pat = defunc_pattern pattern;
          pvb_expr = defunc_expression expression;
          pvb_attributes = attributes;
          pvb_loc = t;
        }
and defunc_case case =
  match case with
  | {
      pc_lhs = pattern;
      pc_guard = expression_option;
      pc_rhs = expression2;
    } -> {
          pc_lhs = defunc_pattern pattern;
          pc_guard = f_option defunc_expression expression_option;
          pc_rhs = defunc_expression expression2;
        }
and defunc_core_type core_type =
  match core_type with
  | {
      ptyp_desc = core_type_desc;
      ptyp_loc = t;
      ptyp_attributes = attributes;
    } -> {
          ptyp_desc = defunc_core_type_desc core_type_desc;
          ptyp_loc = t;
          ptyp_attributes = attributes;
        }
and defunc_core_type_desc core_type_desc =
  match core_type_desc with
  |	Ptyp_any -> Ptyp_any
  |	Ptyp_var string -> Ptyp_var string
  |	Ptyp_arrow (arg_label, core_type1, core_type2) -> Ptyp_arrow (arg_label, defunc_core_type core_type1, defunc_core_type core_type2)
  |	Ptyp_tuple core_type_list -> Ptyp_tuple (List.map defunc_core_type core_type_list)
  |	Ptyp_constr (t, core_type_list) -> Ptyp_constr (t, List.map defunc_core_type core_type_list) 
  |	Ptyp_object ((loc, attributes, core_type)::list, closed_flag) -> Ptyp_object ((loc, attributes, core_type)::list, closed_flag)
  |	Ptyp_class (t, core_type_list) -> Ptyp_class (t, List.map defunc_core_type core_type_list)
  |	Ptyp_alias (core_type, string) -> Ptyp_alias (defunc_core_type core_type, string)
  |	Ptyp_variant (row_field_list, closed_flag, label_list_option) -> Ptyp_variant (row_field_list, closed_flag, label_list_option)
  |	Ptyp_poly (loc_list, core_type) -> Ptyp_poly (loc_list, defunc_core_type core_type)
  |	Ptyp_package package_type -> Ptyp_package package_type
  |	Ptyp_extension extension -> Ptyp_extension extension
and defunc_module_expression module_expr =
  match module_expr with
  | {
      pmod_desc = module_expr_desc;
      pmod_loc = t;
      pmod_attributes = attributes;
    } -> {
      pmod_desc = defunc_module_expression_desc module_expr_desc;
      pmod_loc = t;
      pmod_attributes = attributes;
    }
and defunc_module_expression_desc module_expr_desc =
  match module_expr_desc with
  |	Pmod_ident t -> Pmod_ident t
  |	Pmod_structure structure -> Pmod_structure structure
  |	Pmod_functor (loc, module_type_option, module_expr) -> Pmod_functor (loc, module_type_option, defunc_module_expression module_expr)
  |	Pmod_apply (module_expr1, module_expr2) -> Pmod_apply (defunc_module_expression module_expr1, defunc_module_expression module_expr2)
  |	Pmod_constraint (module_expr, module_type) -> Pmod_constraint (module_expr, module_type)
  |	Pmod_unpack expression -> Pmod_unpack (defunc_expression expression)
  |	Pmod_extension extension -> Pmod_extension extension

let rec case_match_vars vars_tuple =
  match vars_tuple with
  | [] -> []
  | x::xs -> Pat.var {txt = x; loc=(!default_loc)} :: case_match_vars xs

let rec e4 s =
  try
    let attr_vars = Stack.pop s in
    let attr = fst attr_vars in
    let vars = snd attr_vars in
    let body = Hashtbl.find attr_bodies attr in
    let arg = Hashtbl.find attr_args attr in
    Exp.case (Pat.construct {txt = Lident attr; loc=(!default_loc)}
      (if List.length vars > 0
      then Some (Pat.tuple (case_match_vars vars))
      else None))
      (Exp.let_ Nonrecursive [Vb.mk (arg) (Exp.ident {txt = Lident "arg"; loc=(!default_loc)})] body) :: e4 s
  with | Stack.Empty -> []

let e3 v =
  let write = Stack.create () in
  Hashtbl.iter (fun k v -> Stack.push (k, v) write) free_vars;
  Exp.match_ (Exp.ident {txt = Lident "k"; loc=(!default_loc)}) (e4 write)

let e2 v = 
Exp.fun_ Nolabel None (Pat.var {txt = "arg"; loc=(!default_loc)}) (e3 v)

let e1 v = 
Exp.fun_ Nolabel None (Pat.constraint_ (Pat.var {txt = "k"; loc=(!default_loc)}) (Typ.mk (Ptyp_constr ({txt = Lident "kont"; loc=(!default_loc)}, [])))) (e2 v)

let apply v = Vb.mk (Pat.var {txt = "apply"; loc=(!default_loc)}) (e1 v)

(*  free vars becomes empty here?? *)
let rec transform_defunc rec_flag vb_list =
(* let v = Hashtbl.copy free_vars in *)
  Str.value rec_flag (List.map defunc_vb (vb_list@[apply None]))

let rec str_item_defunc_mapper mapper str = 
   begin match str with
      | { pstr_desc =
          Pstr_extension (({ txt = "defun"; loc }, pstr), _attributes); _} -> 
          begin 
            match pstr with
            | PStr [{ pstr_desc =
                    Pstr_value (rec_flag,
                    l); _}] -> transform_defunc rec_flag l
            | _ -> raise (Location.Error (Location.error ~loc "Syntax error in expression mapper"))                       
          end
      (* Delegate to the default mapper. *)
      | x -> default_mapper.structure_item mapper x;
      end

let rec str_defunc_mapper mapper str_list = 
  let res = List.fold_left (fun acc str ->
  (* testar se o str tem o extension defun *)
  begin match str with
  | {pstr_desc = Pstr_extension (({ txt = "defun"; _ }, pstr), _attributes); _} ->
      begin 
      match pstr with
      | PStr [{ pstr_desc =
              Pstr_value (rec_flag,
              l); _}] ->
                (* Gather free variables *)
                List.iter free_vars_value_binding l;
                (* Write continuation type *)
                let write = Stack.create () in
                Hashtbl.iter (fun k v -> Stack.push (k, v) write) free_vars;
                let t = Str.type_ Recursive [
                  Type.mk {txt = "kont"; loc=(!default_loc)}
                  ~kind:(Ptype_variant (build_type write))]
                in
                (* Write defunctionalized function *)
                let exp = str_item_defunc_mapper mapper str in
                exp::t::acc
      | _ -> (str_item_defunc_mapper mapper str)::acc                   
    end
  | x -> (default_mapper.structure_item mapper x)::acc;
  end) [] str_list in
    List.rev res

let rec str_item_print_mapper mapper str = 
   begin match str with
      | { pstr_desc =
          Pstr_extension (({ txt = "print"; _ }, _), _); _} ->
          print_string "%print found \n";
          print_string "\nFree vars: ";
          Hashtbl.iter print_hashtbl_list free_vars;
          print_string "\nVars: ";
          Hashtbl.iter print_hashtbl vars;
          print_string "\nAttributes: ";
          print_queue attributes;
          Str.eval (Exp.constant (Pconst_string ("", None)));
      (* Delegate to the default mapper. *)
      | x -> default_mapper.structure_item mapper x;
      end

let defunc_mapper _argv =
  { 
    default_mapper with
    structure = str_defunc_mapper;
    structure_item = str_item_defunc_mapper
  }

let print_mapper _argv =
  { 
    default_mapper with
    structure_item = str_item_print_mapper
  }

let () = register "defun" defunc_mapper;
         (* register "print" print_mapper *)