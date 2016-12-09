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
  | Print of expression
  | Invalidate of expression * label * variable list
  | Stop
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

exception InvalidJumpTarget of string

let resolve program label =
  let rec do_resolve pc =
    if pc == Array.length program then raise (InvalidJumpTarget label);
    if program.(pc) = Label label then pc
    else do_resolve (pc+1)
  in do_resolve 0

