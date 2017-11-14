module Variable = String

module Label = String

module Address : sig
  type t = private int
  val compare : t -> t -> int
  val fresh : unit -> t
end = struct
  type t = int
  let compare (x : int) y = Pervasives.compare x y
  let counter = ref (-1)
  let fresh () = incr counter; !counter
end

type variable = Variable.t
type label = Label.t

module VarSet = Set.Make(Variable)

module LabelSet = Set.Make(Label)

module Identifier = struct
  type t = string
  let compare = String.compare
end
type identifier = Identifier.t

module Pc = struct
  type t = int
  let compare (x : int) y = Pervasives.compare x y
end

type pc = Pc.t
type address = Address.t

type 'a position = {
  func : label;
  version : label;
  pos : 'a;
}

type instructions = instruction array
and instruction =
  | Decl_var of variable * expression
  | Decl_array of variable * array_def
  | Call of label * variable * expression * (argument list)
  | Return of expression
  | Drop of variable
  | Assign of variable * expression
  | Array_assign of variable * expression * expression
  | Read of variable
  | Branch of expression * label * label
  | Label of label_type
  | Goto of label
  | Print of expression
  | Assert of expression
  | Stop of expression
  | Guard_hint of expression list
  | Assume of {
    label : label;
    guards : expression list;
    target : label position;
    varmap : varmap;
    extra_frames : extra_frame list; }
  | Comment of string
and label_type =
  | MergeLabel of label
  | BranchLabel of label
and array_def =
  | Length of expression
  | List of expression list
and varmap = (variable * expression) list
and extra_frame = {
  varmap : varmap;
  cont_pos : label position;
  cont_res : variable; }
and argument = expression
and expression =
  | Simple of simple_expression
  | Unop of unop * simple_expression
  | Binop of binop * simple_expression * simple_expression
  | Array_index of variable * simple_expression
  | Array_length of simple_expression
and simple_expression =
  | Constant of value
  | Var of variable
and value =
  | Nil
  | Bool of bool
  | Int of int
  | String of string
  | Fun_ref of string
  | Array of address
and unop =
  | Neg
  | Not
and binop =
  | Eq
  | Neq
  | Lt
  | Lte
  | Gt
  | Gte
  | Plus
  | Sub
  | Mult
  | Div
  | Mod
  | And
  | Or

let negate = function
  | Simple (Var x)                  -> Some (Unop (Not, (Var x)))
  | Simple (Constant (Bool false))  -> Some (Simple (Constant (Bool true)))
  | Simple (Constant (Bool true))   -> Some (Simple (Constant (Bool false)))
  | Unop (Not, se)                  -> Some (Simple se)
  | Binop ((Neq|Eq|Gte|Gt|Lte|Lt) as op, e1, e2) ->
      let nop = begin match[@warning "-4"] op with
      | Eq   -> Neq
      | Neq  -> Eq
      | Lt   -> Gte
      | Lte  -> Gt
      | Gt   -> Lte
      | Gte  -> Lt
      | _    -> assert(false)
      end in
      Some (Binop (nop, e1, e2))
  | Simple (Constant (Nil| Int _|Fun_ref _|Array _|String _))
  | Binop ((Plus|Sub|Mult|Div|Mod), _, _)
  | Binop ((And|Or), _, _)  (* TODO *)
  | Unop (Neg, _)
  | Array_index _
  | Array_length _ -> None

type scope_annotation =
  | ExactScope of VarSet.t
  | AtLeastScope of VarSet.t

type inferred_scope =
  | DeadScope
  | Scope of VarSet.t

type annotations = scope_annotation option array

type formal_parameter = Param of variable

type version = {
  label : label;
  instrs : instructions;
  annotations : annotations option;
}
type afunction = {
  name : identifier;
  formals : formal_parameter list;
  body : version list;
}
type program = {
  main : afunction;
  functions : afunction list;
}

type heap_value =
  | Undefined
  | Value of value
  | Block of value array

type binding =
  | Val of value
  | Ref of address

exception Unbound_label of label_type
exception Unbound_bailout_label of label

let resolve_by pred code =
  let rec loop i =
    if i >= Array.length code then raise Not_found
    else match pred code.(i) with
    | Some o -> i+o
    | None -> loop (i + 1)
  in loop 0

let resolve code l =
  let pred = function[@warning "-4"]
      | Label label when label = l -> Some 0
      | _ -> None
  in
  try resolve_by pred code
  with Not_found -> raise (Unbound_label l)

let resolve_bailout code l =
  let pred = function[@warning "-4"]
    | Assume {label} when label = l -> Some 0
    | Call (label, _,_,_) when label = l -> Some 1
    | _ -> None
  in
  try resolve_by pred code
  with Not_found -> raise (Unbound_bailout_label l)

let resolver_by indexer code =
  let tbl = Hashtbl.create 42 in
  let add pc instr = match indexer instr with
    | None -> ()
    | Some (idx, off) ->
      assert (not (Hashtbl.mem tbl idx));
      Hashtbl.add tbl idx (pc+off)
  in
  Array.iteri add code;
  fun index -> Hashtbl.find tbl index

let resolver code =
  let indexer = function[@warning "-4"]
    | Label l -> Some (l, 0)
    | _ -> None
  in
  let resolver = resolver_by indexer code in
  fun l ->
    try resolver l
    with Not_found -> raise (Unbound_label l)

let resolver_bailout code =
  let indexer = function[@warning "-4"]
    | Assume {label} -> Some (label, 0)
    | Call (label, _,_,_) -> Some (label, 1)
    | _ -> None
  in
  let resolver = resolver_by indexer code in
  fun l ->
    try resolver l
    with Not_found -> raise (Unbound_bailout_label l)

let simple_expr_vars = function
  | Var x -> VarSet.singleton x
  | Constant _ -> VarSet.empty

let expr_vars = function
  | Simple e -> simple_expr_vars e
  | Unop (_op, o) ->
    simple_expr_vars o
  | Binop (_op, l, r) ->
    VarSet.union (simple_expr_vars l) (simple_expr_vars r)
  | Array_index (o, i) ->
    VarSet.union (VarSet.singleton o) (simple_expr_vars i)
  | Array_length e ->
    simple_expr_vars e

let arg_vars = expr_vars

let list_vars ls =
  let vs = List.map expr_vars ls in
  List.fold_left VarSet.union VarSet.empty vs

let declared_vars = function
  | Assign _ | Read _ -> VarSet.empty
  | Call (_, x, _, _)
  | Decl_var (x, _) -> VarSet.singleton x
  | Decl_array (x, _) -> VarSet.singleton x
  | ( Drop _
    | Array_assign _
    | Return _
    | Branch _
    | Label _
    | Guard_hint _
    | Goto _
    | Print _
    | Assert _
    | Assume _
    | Comment _
    | Stop _) -> VarSet.empty

let defined_vars = function
  | Assign (x ,_)
  | Read x -> VarSet.singleton x
  | ( Call _
    | Decl_var _
    | Decl_array _
    | Return _
    | Drop _
    | Branch _
    | Label _
    | Goto _
    | Guard_hint _
    | Comment _
    | Print _
    | Assert _
    | Assume _
    | Array_assign _ (* The array has to be defined already. *)
    | Stop _
  ) as e -> declared_vars e

let dropped_vars = function
  | Drop x -> VarSet.singleton x
  | Return _
  | Call _
  | Decl_var _
  | Decl_array _
  | Assign _
  | Array_assign _
  | Read _
  | Branch _
  | Guard_hint _
  | Label _
  | Goto _
  | Comment _
  | Print _
  | Assert _
  | Assume _
  | Stop _ -> VarSet.empty

(* Which variables need to be defined
 * Producer: defined_vars *)
let used_vars = function
  | Assign (_, e) -> expr_vars e
  | Read x -> VarSet.empty
  | Call (_, _x, f, es) ->
    let v = expr_vars f in
    let vs = List.map arg_vars es in
    List.fold_left VarSet.union v vs
  | Stop e
  | Return e -> expr_vars e
  | Decl_var (_x, e) -> expr_vars e
  | Decl_array (_, Length e) -> expr_vars e
  | Decl_array (_, List es) ->
    List.map expr_vars es |> List.fold_left VarSet.union VarSet.empty
  (* the assignee is only required to be in scope, but not used! *)
  | Branch (e, _, _)
  | Print e
  | Assert e
    -> expr_vars e
  | Array_assign (x, i, e) ->
    VarSet.singleton x
    |> VarSet.union (expr_vars i)
    |> VarSet.union (expr_vars e)
  | Drop _
  | Label _
  | Goto _
  | Comment _
  | Guard_hint _
    -> VarSet.empty
  | Assume {guards; varmap; extra_frames} ->
    let fold_cond used guard = VarSet.union used (expr_vars guard) in
    let from_cond = List.fold_left fold_cond VarSet.empty guards in
    let map_vars map = list_vars (List.map (fun (_, e) -> e) map) in
    let fold_map used {varmap} =
      VarSet.union used (map_vars varmap) in
    let from_map = List.fold_left fold_map (map_vars varmap) extra_frames in
    VarSet.union from_cond from_map

(* Which variables need to be in scope
 * Producer: declared_vars *)
let required_vars = function
  | (Assign (x, _)
    | Read x
    | Drop x
    ) as e -> VarSet.add x (used_vars e)
  | ( Call _
    | Stop _
    | Return _
    | Decl_var _
    | Decl_array _
    | Array_assign _
    | Branch _
    | Guard_hint _
    | Label _
    | Goto _
    | Comment _
    | Print _
    | Assert _
    | Assume _
    ) as e -> used_vars e

let changed_vars = function
  | Call (_, x, _, _)
  | Decl_var (x, _) -> VarSet.singleton x
  | Assign (x ,_)
  | Array_assign (x ,_ , _)
  | Drop x
  | Decl_array (x, _)
  | Read x -> VarSet.singleton x
  | Return _
  | Branch _
  | Guard_hint _
  | Label _
  | Goto _
  | Comment _
  | Print _
  | Assert _
  | Assume _
  | Stop _ -> VarSet.empty

exception FunctionDoesNotExist of identifier

let lookup_fun (prog : program) (f : identifier) : afunction =
  if f = "main" then prog.main else
  try List.find (fun {name} -> name = f) prog.functions with
  | Not_found -> raise (FunctionDoesNotExist f)

let replace_fun ({main; functions} as prog : program) (func : afunction) : program =
  let rec replace_fun' rest =
    match rest with
    | [] -> []
    | func' :: rest' ->
      if func'.name = func.name then func :: rest'
      else func' :: replace_fun' rest'
  in
  if (func.name = main.name) then {prog with main = func}
  else {prog with functions = replace_fun' functions}

let get_version (func : afunction) (v : label) : version =
  List.find (fun {label} -> label = v) func.body

let active_version (func : afunction) : version =
  (List.hd func.body)

let replace_active_version (func : afunction) (repl : version) : afunction =
  { func with
    body = repl :: (List.tl func.body); }

let checkpoint_prefix = "cp_"
let checkpoint_label pc =
  checkpoint_prefix ^ (string_of_int pc)

let pcs (instrs : instructions) : pc array =
  Array.mapi (fun pc _ -> pc) instrs

let is_checkpoint = function[@warning "-4"]
  | Assume _ -> true
  | _ -> false

let checkpoints (instrs : instructions) =
  let pcs = Array.to_list (pcs instrs) in
  List.filter (fun pc -> is_checkpoint instrs.(pc)) pcs

let has_checkpoint =
  Array.exists is_checkpoint

let independent instr exp =
  VarSet.is_empty (VarSet.inter (changed_vars instr) (expr_vars exp))

class map = object (m)
  method variable_use x = x
  method variable_assign x = x
  method binder x = x
  method varmap_binder x = x

  method value v = v

  method simple_expression = function
    | Constant v ->
      Constant (m#value v)
    | Var x ->
      Var (m#variable_use x)
  method expression = function
    | Simple e ->
      Simple (m#simple_expression e)
    | Unop (op, o) ->
      Unop (op, m#simple_expression o)
    | Binop (op, l, r) ->
      Binop (op, m#simple_expression l, m#simple_expression r)
    | Array_index (o, i) ->
      Array_index (m#variable_use o, m#simple_expression i)
    | Array_length e ->
      Array_length (m#simple_expression e)

  method goto_label l = l
  method branch_label l = l
  method bailout_label l = l

  method instruction = function
    | Decl_var (x, e) ->
      Decl_var (m#binder x, m#expression e)
    | Decl_array (x, def) ->
      Decl_array (m#binder x, m#array_def def)
    | Call (l, x, e, args) ->
      Call (m#bailout_label l, m#binder x, m#expression e, List.map m#argument args)
    | Return e ->
      Return (m#expression e)
    | Drop x ->
      Drop (m#variable_assign x)
    | Assign (x, e) ->
      Assign (m#variable_assign x, m#expression e)
    | Array_assign (x, e, idx) ->
      Array_assign (m#variable_assign x, m#expression e, m#expression idx)
    | Read x ->
      Read (m#variable_assign x)
    | Branch (e, l1, l2) ->
      Branch (m#expression e, m#branch_label l1, m#branch_label l2)
    | Label (MergeLabel l) ->
      Label (MergeLabel (m#goto_label l))
    | Label (BranchLabel l) ->
      Label (BranchLabel (m#branch_label l))
    | Goto l ->
      Goto (m#goto_label l)
    | Print e ->
      Print (m#expression e)
    | Assert e ->
      Assert (m#expression e)
    | Guard_hint es ->
      Guard_hint (List.map m#expression es)
    | Stop e ->
      Stop (m#expression e)
    | Assume {label; guards; target; varmap; extra_frames} ->
      Assume {
        label = m#bailout_label label;
        guards = List.map m#expression guards;
        target = m#osr_target target;
        varmap = m#osr_varmap varmap;
        extra_frames = List.map m#extra_frame extra_frames;
      }
    | Comment s ->
      Comment s
  method argument e = m#expression e
  method array_def = function
    | Length e ->
      Length (m#expression e)
    | List es ->
      List (List.map m#expression es)

  method osr_func_label l = l
  method osr_version_label l = l
  method osr_target_label l = l

  method osr_target {func; version; pos} = {
    func = m#osr_func_label func;
    version = m#osr_version_label version;
    pos = m#osr_target_label pos }

  method frame_cont_res res = res
  method extra_frame {varmap; cont_pos; cont_res} = {
    varmap = m#osr_varmap varmap;
    cont_pos = m#osr_target cont_pos;
    cont_res = m#frame_cont_res cont_res;
  }
  method osr_varmap = List.map m#osr_varmap_entry
  method osr_varmap_entry = function
    | x, e -> m#varmap_binder x, m#expression e
end
