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

module Pc = struct
  type t = int
  let compare (x : int) y = Pervasives.compare x y
end

type pc = Pc.t

type program = instruction array
and instruction =
  | Decl_const of variable * expression
  | Decl_mut of variable * (expression option)
  | Assign of variable * expression
  | Branch of expression * label * label
  | Label of label
  | Goto of label
  | Read of variable
  | Print of expression
  | Invalidate of expression * label * variable list
  | Stop
  | Comment of string
and expression =
  | Simple of simple_expression
  | Op of primop * simple_expression list
and simple_expression =
  | Lit of litteral
  | Var of variable
and litteral =
  | Nil
  | Bool of bool
  | Int of int
and primop =
  | Eq
  | Neq
  | Plus

type value =
  | Lit of litteral

type heap_value =
  | Undefined
  | Value of value

type address = Address.t

type binding =
  | Const of value
  | Mut of address

let string_of_litteral : litteral -> string = function
  | Nil -> "nil"
  | Bool b -> string_of_bool b
  | Int n -> string_of_int n

let litteral_of_string : string -> litteral = function
  | "nil" -> Nil
  | "true" -> Bool true
  | "false" -> Bool false
  | n ->
    try Int (int_of_string n) with _ ->
      Printf.kprintf invalid_arg "litteral_of_string %S" n

let string_of_value (Lit lit) = string_of_litteral lit
let value_of_string str : value = Lit (litteral_of_string str)

exception Unbound_label of label

let resolve (code : program) (label : string) =
  let rec loop i =
    if i >= Array.length code then raise (Unbound_label label)
    else if code.(i) = Label label then i
    else loop (i + 1)
  in loop 0

module VarSet = Set.Make(Variable)

let simple_expr_vars = function
  | Var x -> VarSet.singleton x
  | Lit _ -> VarSet.empty

let expr_vars = function
  | Simple e -> simple_expr_vars e
  | Op (_op, xs) ->
    List.map simple_expr_vars xs
    |> List.fold_left VarSet.union VarSet.empty

let declared_vars = function
  | Decl_const (x, _)
  | Decl_mut (x, _) -> VarSet.singleton x
  | (Assign _
    | Branch _
    | Label _
    | Goto _
    | Read _
    | Print _
    | Invalidate _
    | Comment _
    | Stop) -> VarSet.empty

(* Which variables need to be in scope
 * Producer: declared_vars *)
let required_vars = function
  | Decl_const (_x, e) -> expr_vars e
  | Decl_mut (_x, Some e) -> expr_vars e
  | Decl_mut (_x, None) -> VarSet.empty
  | Assign (x, e) -> VarSet.union (VarSet.singleton x) (expr_vars e)
  | Branch (e, _l1, _l2) -> expr_vars e
  | Label _l | Goto _l -> VarSet.empty
  | Comment _ -> VarSet.empty
  | Read x -> VarSet.singleton x
  | Print e -> expr_vars e
  | Invalidate (e, _l, xs) ->
    VarSet.union (VarSet.of_list xs) (expr_vars e)
  | Stop -> VarSet.empty

let defined_vars = function
  | Decl_const (x, _)
  | Decl_mut (x, Some _)
  | Assign (x ,_)
  | Read x -> VarSet.singleton x
  | Decl_mut (_, None)
  | Branch _
  | Label _
  | Goto _
  | Comment _
  | Print _
  | Invalidate _
  | Stop -> VarSet.empty

(* Which variables need to be defined
 * Producer: defined_vars *)
let used_vars = function
  | Decl_const (_x, e) -> expr_vars e
  | Decl_mut (_x, Some e) -> expr_vars e
  | Decl_mut (_x, None) -> VarSet.empty
  (* the assignee is only required to be in scope, but not used! *)
  | Assign (x, e) -> expr_vars e
  | Branch (e, _l1, _l2) -> expr_vars e
  | Label _l | Goto _l -> VarSet.empty
  | Comment _ -> VarSet.empty
  | Read _ -> VarSet.empty
  | Print e -> expr_vars e
  | Invalidate (e, _l, xs) ->
    VarSet.union (VarSet.of_list xs) (expr_vars e)
  | Stop -> VarSet.empty

type scope_annotation =
  | Exact of VarSet.t
  | At_least of VarSet.t

type inferred_scope =
  | Dead
  | Scope of VarSet.t

type annotated_program = (program * scope_annotation option array)
