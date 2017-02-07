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

type instruction_stream = instruction array
and instruction =
  | Decl_const of variable * expression
  | Decl_mut of variable * (expression option)
  | Drop of variable
  | Assign of variable * expression
  | Clear of variable
  | Read of variable
  | Branch of expression * label * label
  | Label of label
  | Goto of label
  | Print of expression
  | Osr of expression * label * label * osr_def list
  | Stop
  | Comment of string
and osr_def =
  | OsrConst of variable * expression
  | OsrMut of variable * ext_expression
and expression =
  | Simple of simple_expression
  | Op of primop * simple_expression list
and ext_expression =
  | OsrExp of expression
  | OsrUndef
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

let resolve (code : instruction_stream) (label : string) =
  let rec loop i =
    if i >= Array.length code then raise (Unbound_label label)
    else if code.(i) = Label label then i
    else loop (i + 1)
  in loop 0

module VarSet = Set.Make(Variable)

type typed_var =
  | Mut_var of string
  | Const_var of string

exception Incomparable

module TypedVar = struct
  type t = typed_var
  let compare a b =
    match (a,b) with
    | Mut_var   a, Mut_var   b
    | Const_var a, Const_var b -> String.compare a b
    | Mut_var   a, Const_var b
    | Const_var a, Mut_var   b ->
      if a = b then raise Incomparable else String.compare a b
end

module TypedVarSet = struct
  include Set.Make(TypedVar)

  let vars set =
    List.map (fun v ->
        match v with
        | Mut_var x | Const_var x -> x)
      (elements set)

  let untyped set = VarSet.of_list (vars set)

  let muts set =
    let muts = filter (fun v ->
        match v with
        | Mut_var x -> true
        | Const_var x -> false)
      set in
    untyped muts

  let diff_untyped typed untyped =
    filter (fun e ->
        match e with
        | Mut_var x | Const_var x ->
          begin match VarSet.find x untyped with
            | exception Not_found -> true
            | _ -> false
          end) typed

  let inter_untyped typed untyped =
    filter (fun e ->
        match e with
        | Mut_var x | Const_var x ->
          begin match VarSet.find x untyped with
            | exception Not_found -> false
            | _ -> true
          end) typed
end

let simple_expr_vars = function
  | Var x -> VarSet.singleton x
  | Lit _ -> VarSet.empty

let expr_vars = function
  | Simple e -> simple_expr_vars e
  | Op (_op, xs) ->
    List.map simple_expr_vars xs
    |> List.fold_left VarSet.union VarSet.empty

let declared_vars = function
  | Decl_const (x, _) -> TypedVarSet.singleton (Const_var x)
  | Decl_mut (x, _) -> TypedVarSet.singleton (Mut_var x)
  | (Assign _
    | Drop _
    | Clear _
    | Branch _
    | Label _
    | Goto _
    | Read _
    | Print _
    | Osr _
    | Comment _
    | Stop) -> TypedVarSet.empty

(* Which variables need to be in scope
 * Producer: declared_vars *)
let required_vars = function
  | Decl_const (_x, e) -> expr_vars e
  | Decl_mut (_x, Some e) -> expr_vars e
  | Decl_mut (_x, None) -> VarSet.empty
  | Drop x | Clear x | Read x -> VarSet.singleton x
  | Assign (x, e) -> VarSet.union (VarSet.singleton x) (expr_vars e)
  | Branch (e, _l1, _l2) -> expr_vars e
  | Label _l | Goto _l -> VarSet.empty
  | Comment _ -> VarSet.empty
  | Print e -> expr_vars e
  | Osr (e, _, _, osr) ->
    let exps = List.map (function
        | OsrConst (_, e) -> e
        | OsrMut (_, OsrExp e) -> e
        | OsrMut (_, OsrUndef) -> Simple (Lit Nil)) osr in
    let exps_vars = List.map expr_vars exps in
    List.fold_left VarSet.union (expr_vars e) exps_vars
  | Stop -> VarSet.empty

let defined_vars = function
  | Decl_const (x, _) -> TypedVarSet.singleton (Const_var x)
  | Decl_mut (x, Some _)
  | Assign (x ,_)
  | Read x -> TypedVarSet.singleton (Mut_var x)
  | Decl_mut (_, None)
  | Drop _
  | Clear _
  | Branch _
  | Label _
  | Goto _
  | Comment _
  | Print _
  | Osr _
  | Stop -> TypedVarSet.empty

let dropped_vars = function
  | Drop x -> VarSet.singleton x
  | Decl_const _
  | Decl_mut _
  | Assign _
  | Clear _
  | Read _
  | Branch _
  | Label _
  | Goto _
  | Comment _
  | Print _
  | Osr _
  | Stop -> VarSet.empty

let cleared_vars = function
  | Clear x -> VarSet.singleton x
  | Decl_const _
  | Decl_mut _
  | Assign _
  | Drop _
  | Read _
  | Branch _
  | Label _
  | Goto _
  | Comment _
  | Print _
  | Osr _
  | Stop -> VarSet.empty

(* Which variables need to be defined
 * Producer: defined_vars *)
let used_vars = function
  | Decl_const (_x, e) -> expr_vars e
  | Decl_mut (_x, Some e) -> expr_vars e
  | Decl_mut (_x, None) -> VarSet.empty
  (* the assignee is only required to be in scope, but not used! *)
  | Assign (_, e)
  | Branch (e, _, _)
  | Print e -> expr_vars e
  | Drop _
  | Clear _
  | Label _
  | Goto _
  | Comment _
  | Read _
  | Stop -> VarSet.empty
  | Osr (e, _, _, osr) ->
    let exps = List.map (function
        | OsrConst (_, e) -> e
        | OsrMut (_, OsrExp e) -> e
        | OsrMut (_, OsrUndef) -> Simple (Lit Nil)) osr in
    let exps_vars = List.map expr_vars exps in
    List.fold_left VarSet.union (expr_vars e) exps_vars

type scope_annotation =
  | Exact of VarSet.t
  | At_least of VarSet.t

type inferred_scope =
  | Dead
  | Scope of TypedVarSet.t

type segment = instruction_stream * scope_annotation option array
type program_ = (string * segment) list


module Value = struct
  let int n : value = Lit (Int n)
  let bool b : value = Lit (Bool b)
end
