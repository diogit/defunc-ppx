open Ppxlib

let ppx_name = "defun"
(*let free_vars = Hashtbl.create 16*)

let print_attributes attributes =
if List.length attributes > 0 then print_string (List.hd attributes).attr_name.txt

let get_attributes expr =
  match expr with
  | {
    pexp_desc = expression_desc;
    pexp_loc = location;
    pexp_loc_stack = location_stack;
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

let rec iterate_value_binding_list (value_binding_list : Ppxlib.value_binding list) =
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

let do_thing structure_item_desc = 
  let value_binding_list = get_value_binding structure_item_desc in
  let value_binding = iterate_value_binding_list value_binding_list in
  let value_binding_expression = get_value_binding_expression value_binding in
  let attributes = get_attributes value_binding_expression in
  print_attributes attributes

let expand ~ctxt pstr =
  let loc = Expansion_context.Extension.extension_point_loc ctxt in
  match pstr with
  | {
    pstr_desc = structure_item_desc;
    pstr_loc = location
    } -> do_thing structure_item_desc; pstr
  | _ -> Location.raise_errorf ~loc "Expected an integer expression"

let my_extension =
  Extension.V3.declare
    "defun"
    Extension.Context.structure_item
    Ast_pattern.(single_expr_payload __)
    expand

let rule = Ppxlib.Context_free.Rule.extension my_extension

let () =
  Driver.register_transformation
    ~rules:[rule]
    "defun"