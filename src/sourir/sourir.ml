module Variable = struct
  type t = string
  let compare = String.compare
end

module Label = struct
  type t = int
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

type program = (label * instruction) list
and instruction =
  | Decl_const of variable * expression
  | Decl_mut of variable * expression
  | Assign of variable * expression
  | Branch of expression * label * label
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
and primop = Eq

type value =
  | Lit of litteral

type address = Address.t

type binding =
  | Const of value
  | Mut of address

module Env = Map.Make(Variable)
module Heap = Map.Make(Address)

type trace = value list
type environment = binding Env.t
type heap = value Heap.t

type configuration = {
  trace : trace;
  heap : heap;
  env : environment;
  program : program;
  pc : label;
}

type litteral_type = Nil | Bool | Int
let litteral_type : litteral -> litteral_type = function
  | Nil -> Nil
  | Bool _ -> Bool
  | Int _ -> Int

exception Unbound_variable of variable
exception Invalid_heap
exception Arity_error of primop
exception Invalid_update

let lookup heap env x =
  match Env.find x env with
  | exception Not_found -> raise (Unbound_variable x)
  | Const v -> v
  | Mut a ->
    begin match Heap.find a heap with
    | exception Not_found -> raise Invalid_heap
    | v -> v
    end

let update heap env x v =
  match Env.find x env with
  | exception Not_found -> raise (Unbound_variable x)
  | Const _ -> raise Invalid_update
  | Mut a ->
    begin match Heap.find a heap with
    | exception Not_found -> raise Invalid_heap
    | _ -> Heap.add a v heap
    end  

let litteral_eq (lit1 : litteral) (lit2 : litteral) =
  match lit1, lit2 with
  | Nil, Nil -> true
  | Nil, _ | _, Nil -> false
  | Bool b1, Bool b2 -> b1 = b2
  | Bool _, _ | _, Bool _ -> false
  | Int n1, Int n2 -> n1 = n2

let value_eq (Lit lit1) (Lit lit2) = litteral_eq lit1 lit2

let rec eval heap env = function
  | Var x -> lookup heap env x
  | Lit lit -> Lit lit
  | Op (Eq, [x1; x2]) ->
    let v1 = eval heap env (Var x1) in
    let v2 = eval heap env (Var x2) in
    Lit (Bool (value_eq v1 v2))
  | Op (Eq, _) -> raise (Arity_error Eq)

type type_error = {
  expected : litteral_type;
  received : litteral_type;
}

exception Unbound_label of label
exception Type_error of type_error

let get_bool (Lit lit : value) = 
  match lit with
  | Bool b -> b
  | other -> 
     let expected, received = Bool, litteral_type other in
     raise (Type_error { expected; received })

let reduce conf =
  let eval conf e = eval conf.heap conf.env e in
  let pc' = conf.pc + 1 in
  match List.assoc conf.pc conf.program with
  | exception Not_found -> raise (Unbound_label conf.pc)
  | Stop -> conf
  | Decl_const (x, e) -> 
     let v = eval conf e in
     { conf with
       env = Env.add x (Const v) conf.env;
       pc = pc';
     }
  | Decl_mut (x, e) ->
     let a = Address.fresh () in
     let v = eval conf e in
     { conf with
       heap = Heap.add a v conf.heap;
       env = Env.add x (Mut a) conf.env;
       pc = pc';
     }
  | Assign (x, e) ->
     let v = eval conf e in
     { conf with
       heap = update conf.heap conf.env x v;
       pc = pc';
     }
  | Branch (e, l1, l2) ->
     let b = get_bool (eval conf e) in
     { conf with pc = if b then l1 else l2 }
  | Goto pc -> { conf with pc }
  | Print e ->
     let v = eval conf e in
     { conf with
       trace = v :: conf.trace;
       pc = pc';
     }
  | Invalidate (e, l, xs) ->
     let b = get_bool (eval conf e) in
     if b then
       { conf with
         pc = pc';
       }
     else begin
       let add env x =
         match Env.find x conf.env with
         | exception Not_found -> raise (Unbound_variable x)
         | v -> Env.add x v env
       in
       let new_env = List.fold_left add Env.empty xs in
       { conf with
         pc = l;
         env = new_env }
     end

let rec reduce_bounded (conf, n) =
  if n == 0 then conf
  else let conf = reduce conf in
    reduce_bounded (conf, n - 1)

let start program pc = {
  trace = [];
  heap = Heap.empty;
  env = Env.empty;
  program;
  pc;
}

let stop conf = List.assoc conf.pc conf.program = Stop

let run_bounded (prog, n) =
  let conf = start prog 1 in
    reduce_bounded (conf, n)
