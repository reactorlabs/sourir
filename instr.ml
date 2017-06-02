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
  | Call of variable * expression * (argument list)
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
  | Osr of {label : label; cond : expression list; target : label position; map : osr_def list; }
  | Comment of string
and label_type =
  | MergeLabel of label
  | BranchLabel of label
and array_def =
  | Length of expression
  | List of expression list
and osr_def =
  | Osr_var of variable * expression
and argument = expression
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
  | Neg
  | Plus
  | Sub
  | Mult
  | Div
  | Mod
  | Not
  | And
  | Or
  | Array_index
  | Array_length

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
exception Unbound_osr_label of label

let resolve (code : instructions) (label : label_type) =
  let rec loop i =
    if i >= Array.length code then raise (Unbound_label label)
    else if code.(i) = Label label then i
    else loop (i + 1)
  in loop 0

let resolve_osr (code : instructions) (l : string) =
  let rec loop i =
    if i >= Array.length code then raise (Unbound_osr_label l)
    else match[@warning "-4"] code.(i) with
         | Osr {label} when label = l -> i
         | _ -> loop (i + 1)
  in loop 0

let simple_expr_vars = function
  | Var x -> VarSet.singleton x
  | Constant _ -> VarSet.empty

let expr_vars = function
  | Simple e -> simple_expr_vars e
  | Op (_op, xs) ->
    List.map simple_expr_vars xs
    |> List.fold_left VarSet.union VarSet.empty

let arg_vars = expr_vars

let list_vars ls =
  let vs = List.map expr_vars ls in
  List.fold_left VarSet.union VarSet.empty vs

let declared_vars = function
  | Assign _ | Read _ -> VarSet.empty
  | Call (x, _, _)
  | Decl_var (x, _) -> VarSet.singleton x
  | Decl_array (x, _) -> VarSet.singleton x
  | ( Drop _
    | Array_assign _
    | Return _
    | Branch _
    | Label _
    | Goto _
    | Print _
    | Assert _
    | Osr _
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
    | Comment _
    | Print _
    | Assert _
    | Osr _
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
  | Label _
  | Goto _
  | Comment _
  | Print _
  | Assert _
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
    -> VarSet.empty
  | Osr {cond; map} ->
    let exps = List.map (fun (Osr_var (_, e)) -> e) map in
    VarSet.union (list_vars cond) (list_vars exps)

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
    | Label _
    | Goto _
    | Comment _
    | Print _
    | Assert _
    | Osr _
    ) as e -> used_vars e

let changed_vars = function
  | Call (x, _, _)
  | Decl_var (x, _) -> VarSet.singleton x
  | Assign (x ,_)
  | Array_assign (x ,_ , _)
  | Drop x
  | Decl_array (x, _)
  | Read x -> VarSet.singleton x
  | Return _
  | Branch _
  | Label _
  | Goto _
  | Comment _
  | Print _
  | Assert _
  | Osr _
  | Stop _ -> VarSet.empty

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

let checkpoint_prefix = "cp_"
let checkpoint_label pc =
  checkpoint_prefix ^ (string_of_int pc)

let independent instr exp =
  VarSet.is_empty (VarSet.inter (changed_vars instr) (expr_vars exp))

class map = object (m)
  method variable_use x = x
  method variable_assign x = x
  method binder x = x

  method value v = v

  method primop op = op

  method simple_expression = function
    | Constant v ->
      Constant (m#value v)
    | Var x ->
      Var (m#variable_use x)
  method expression = function
    | Simple e ->
      Simple (m#simple_expression e)
    | Op (op, es) ->
      Op (m#primop op, List.map m#simple_expression es)

  method goto_label l = l
  method branch_label l = l

  method func l = l
  method version l = l
  method pos l = l

  method unique_pos {func; version; pos} = {
    func = m#func func;
    version = m#version version;
    pos = m#pos pos;
  }
  method instruction = function
    | Decl_var (x, e) ->
      Decl_var (m#binder x, m#expression e)
    | Decl_array (x, def) ->
      Decl_array (m#binder x, m#array_def def)
    | Call (x, e, args) ->
      Call (m#binder x, m#expression e, List.map m#argument args)
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
    | Stop e ->
      Stop (m#expression e)
    | Osr {label; cond; target; map} ->
      Osr {
        label;
        cond = List.map m#expression cond;
        target = m#unique_pos target;
        map = List.map m#osr_map map;
      }
    | Comment s ->
      Comment s
  method argument e = m#expression e
  method array_def = function
    | Length e ->
      Length (m#expression e)
    | List es ->
      List (List.map m#expression es)
  method osr_map = function
    | Osr_var (x, e) ->
      Osr_var (m#binder x, m#expression e)
end
