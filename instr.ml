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
  | Decl_mut of variable * expression
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
  | Lit of litteral
  | Var of variable
  | Op of primop * variable list
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

let bound_vars = function
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

let expr_vars = function
  | Var x -> VarSet.singleton x
  | Lit _ -> VarSet.empty
  | Op (_op, xs) -> VarSet.of_list xs

let free_vars = function
  | Decl_const (_x, e) -> expr_vars e
  | Decl_mut (_x, e) -> expr_vars e
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
  | Decl_mut (x, _)
  | Assign (x ,_) -> Some x
  | _ -> None

let consumed_vars exp =
  let res = match exp with
  | Decl_const (_x, e) -> expr_vars e
  | Decl_mut (_x, e) -> expr_vars e
  (* In Scope.free_vars the assignee is considered free as well *)
  | Assign (x, e) -> expr_vars e
  | Branch (e, _l1, _l2) -> expr_vars e
  | Label _l | Goto _l -> VarSet.empty
  | Comment _ -> VarSet.empty
  | Read x -> VarSet.singleton x
  | Print e -> expr_vars e
  | Invalidate (e, _l, xs) ->
    VarSet.union (VarSet.of_list xs) (expr_vars e)
  | Stop -> VarSet.empty
  in
  VarSet.elements res


