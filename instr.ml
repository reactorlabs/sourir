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
and primop = Eq | Plus

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
