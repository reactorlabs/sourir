module Variable = struct
  type t = string
  let compare = String.compare
end

module Label = struct
  type t = string
  let compare = String.compare
end

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

type variable_type = Mut_var | Const_var

type moded_var = variable_type * variable

exception Incomparable

module ModedVar = struct
  type t = moded_var
  let compare (ma, a) (mb, b) =
    match String.compare a b with
    | 0 ->
      if ma = mb then 0 else raise Incomparable
    | c -> c
end

module ModedVarSet = struct
  include Set.Make(ModedVar)

  let vars set = List.map snd (elements set)
  let untyped set = VarSet.of_list (vars set)

  let muts set =
    let muts = filter (fun (m,v) -> m = Mut_var) set in
    untyped muts

  let diff_untyped typed untyped =
    filter (fun (_m, x) -> not (VarSet.mem x untyped)) typed

  let inter_untyped typed untyped =
    filter (fun (_m, x) -> VarSet.mem x untyped) typed
end

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

type unique_pos = {func : label; version : label; label : label;}

type instructions = instruction array
and instruction =
  | Decl_const of variable * expression
  | Decl_mut of variable * (expression option)
  | Decl_array of variable * array_def
  | Call of variable * expression * (argument list)
  | Return of expression
  | Drop of variable
  | Assign of variable * expression
  | Array_assign of variable * expression * expression
  | Clear of variable
  | Read of variable
  | Branch of expression * label * label
  | Label of label
  | Goto of label
  | Print of expression
  | Stop of expression
  | Osr of {cond : expression list; target : unique_pos; map : osr_def list; }
  | Comment of string
and array_def =
  | Length of expression
  | List of expression list
and osr_def =
  | Osr_const of variable * expression
  | Osr_mut of variable * expression
  | Osr_mut_ref of variable * variable
  | Osr_mut_undef of variable
and argument =
  | Arg_by_val of expression
  | Arg_by_ref of variable
and expression =
  | Simple of simple_expression
  | Op of primop * simple_expression list
and simple_expression =
  | Constant of value
  | Var of variable
and value =
  | Nil
  | Bool of bool
  | Int of int
  | Fun_ref of string
  | Array of address
and primop =
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
  | Array_index
  | Array_length

type scope_annotation =
  | ExactScope of VarSet.t
  | AtLeastScope of VarSet.t

type inferred_scope =
  | DeadScope
  | Scope of ModedVarSet.t

type annotations = scope_annotation option array

type formal_parameter =
  | Const_val_param of variable
  | Mut_ref_param of variable

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
type analysis_input = {
  formals : ModedVarSet.t;
  instrs : instructions;
}

type heap_value =
  | Undefined
  | Value of value
  | Block of value array

type binding =
  | Val of value
  | Ref of address

exception Unbound_label of label

let resolve (code : instructions) (label : string) =
  let rec loop i =
    if i >= Array.length code then raise (Unbound_label label)
    else if code.(i) = Label label then i
    else loop (i + 1)
  in loop 0

let simple_expr_vars = function
  | Var x -> VarSet.singleton x
  | Constant _ -> VarSet.empty

let expr_vars = function
  | Simple e -> simple_expr_vars e
  | Op (_op, xs) ->
    List.map simple_expr_vars xs
    |> List.fold_left VarSet.union VarSet.empty

let arg_vars = function
  | Arg_by_val e -> expr_vars e
  | Arg_by_ref x -> VarSet.singleton x

let list_vars ls =
  let vs = List.map expr_vars ls in
  List.fold_left VarSet.union VarSet.empty vs

let declared_vars = function
  | Assign _ | Read _ -> ModedVarSet.empty
  | Call (x, _, _)
  | Decl_const (x, _) -> ModedVarSet.singleton (Const_var, x)
  | Decl_mut (x, _) -> ModedVarSet.singleton (Mut_var, x)
  | Decl_array (x, _) -> ModedVarSet.singleton (Const_var, x)
  | ( Drop _
    | Array_assign _
    | Return _
    | Clear _
    | Branch _
    | Label _
    | Goto _
    | Print _
    | Osr _
    | Comment _
    | Stop _) -> ModedVarSet.empty

let defined_vars = function
  | Decl_mut (x, None) -> ModedVarSet.empty
  | Assign (x ,_)
  | Read x -> ModedVarSet.singleton (Mut_var, x)
  | ( Call _
    | Decl_const _
    | Decl_mut (_, Some _)
    | Decl_array _
    | Return _
    | Drop _
    | Clear _
    | Branch _
    | Label _
    | Goto _
    | Comment _
    | Print _
    | Osr _
    | Array_assign _ (* The array has to be defined already. *)
    | Stop _
  ) as e -> declared_vars e

let dropped_vars = function
  | Drop x -> VarSet.singleton x
  | Return _
  | Call _
  | Decl_const _
  | Decl_mut _
  | Decl_array _
  | Assign _
  | Array_assign _
  | Clear _
  | Read _
  | Branch _
  | Label _
  | Goto _
  | Comment _
  | Print _
  | Osr _
  | Stop _ -> VarSet.empty

let cleared_vars = function
  | Clear x -> VarSet.singleton x
  | Return _
  | Call _
  | Decl_const _
  | Decl_mut _
  | Decl_array _
  | Assign _
  | Array_assign _
  | Drop _
  | Read _
  | Branch _
  | Label _
  | Goto _
  | Comment _
  | Print _
  | Osr _
  | Stop _ -> VarSet.empty


(* Which variables need to be defined
 * Producer: defined_vars *)
let used_vars = function
  | Assign (_, e) -> expr_vars e
  | Read x -> VarSet.empty
  | Call (_x, f, es) ->
    let v = expr_vars f in
    let vs = List.map arg_vars es in
    List.fold_left VarSet.union v vs
  | Stop e
  | Return e -> expr_vars e
  | Decl_const (_x, e) -> expr_vars e
  | Decl_mut (_x, Some e) -> expr_vars e
  | Decl_mut (_x, None) -> VarSet.empty
  | Decl_array (_, Length e) -> expr_vars e
  | Decl_array (_, List es) ->
    List.map expr_vars es |> List.fold_left VarSet.union VarSet.empty
  (* the assignee is only required to be in scope, but not used! *)
  | Branch (e, _, _)
  | Print e -> expr_vars e
  | Array_assign (x, i, e) ->
    VarSet.singleton x
    |> VarSet.union (expr_vars i)
    |> VarSet.union (expr_vars e)
  | Drop _
  | Clear _
  | Label _
  | Goto _
  | Comment _
    -> VarSet.empty
  | Osr {cond; map} ->
    let exps = List.map (function
        | Osr_const (_, e) -> e
        | Osr_mut (_, e) -> e
        | Osr_mut_ref (_, x) -> Simple (Var x)
        | Osr_mut_undef _ -> Simple (Constant Nil)) map in
    VarSet.union (list_vars cond) (list_vars exps)

(* Which variables need to be in scope
 * Producer: declared_vars *)
let required_vars = function
  | (Assign (x, _)
    | Read x
    | Drop x
    | Clear x
    ) as e -> VarSet.add x (used_vars e)
  | ( Call _
    | Stop _
    | Return _
    | Decl_const _
    | Decl_mut _
    | Decl_array _
    | Array_assign _
    | Branch _
    | Label _
    | Goto _
    | Comment _
    | Print _
    | Osr _
    ) as e -> used_vars e

let changed_vars = function
  | Call (x, _, _)
  | Decl_const (x, _) -> ModedVarSet.singleton (Const_var, x)
  | Decl_mut (x, Some _)
  | Assign (x ,_)
  | Array_assign (x ,_ , _)
  | Drop x
  | Clear x
  | Decl_mut (x, None)
  | Decl_array (x, _)
  | Read x -> ModedVarSet.singleton (Mut_var, x)
  | Return _
  | Branch _
  | Label _
  | Goto _
  | Comment _
  | Print _
  | Osr _
  | Stop _ -> ModedVarSet.empty

exception FunctionDoesNotExist of identifier

let lookup_fun (prog : program) (f : identifier) : afunction =
  if f = "main" then prog.main else
  try List.find (fun {name} -> name = f) prog.functions with
  | Not_found -> raise (FunctionDoesNotExist f)

let get_version (func : afunction) (v : label) : version =
  List.find (fun {label} -> label = v) func.body

let active_version (func : afunction) : version =
  (List.hd func.body)

let replace_active_version (func : afunction) (repl : version) : afunction =
  { func with
    body = repl :: (List.tl func.body); }

module Value = struct
  let int n : value = Int n
  let bool b : value = Bool b
end

let checkpoint_prefix = "checkpoint_"
let is_checkpoint_label l =
  let len = String.length checkpoint_prefix in
  String.length l > len && (String.sub l 0 11) = checkpoint_prefix
let checkpoint_label pc =
  checkpoint_prefix ^ (string_of_int pc)

let independent instr exp =
  let changed = ModedVarSet.untyped (changed_vars instr) in
  VarSet.is_empty (VarSet.inter changed (expr_vars exp))
