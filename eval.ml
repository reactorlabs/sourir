open Instr

module Env = Map.Make(Variable)
module Heap = Map.Make(Address)

type trace = value list
type environment = binding Env.t
type heap = value Heap.t

type pc = int

type status = Running | Stopped

type configuration = {
  trace : trace;
  heap : heap;
  env : environment;
  program : program;
  pc : pc;
  status : status;
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

type type_error = {
  expected : litteral_type;
  received : litteral_type;
}
exception Type_error of type_error
type product_type_error = {
  expected : litteral_type * litteral_type;
  received : litteral_type * litteral_type;
}
exception ProductType_error of product_type_error

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

let litteral_plus (lit1 : litteral) (lit2 : litteral) =
  match lit1, lit2 with
  | Int n1, Int n2 -> n1 + n2
  | x1, x2 ->
      let expected = (Int, Int) in
      let received = litteral_type x1, litteral_type x2 in
      raise (ProductType_error { expected; received })


let value_eq (Lit lit1) (Lit lit2) = litteral_eq lit1 lit2
let value_plus (Lit lit1) (Lit lit2) = litteral_plus lit1 lit2

let rec eval heap env = function
  | Var x -> lookup heap env x
  | Lit lit -> Lit lit
  | Op (Eq, [x1; x2]) ->
    let v1 = eval heap env (Var x1) in
    let v2 = eval heap env (Var x2) in
    Lit (Bool (value_eq v1 v2))
  | Op (Plus, [x1; x2]) ->
    let v1 = eval heap env (Var x1) in
    let v2 = eval heap env (Var x2) in
    Lit (Int (value_plus v1 v2))
  | Op (primop, _) -> raise (Arity_error Eq)

let get_int (Lit lit : value) =
  match lit with
  | Int n -> n
  | other ->
     let expected, received = Int, litteral_type other in
     raise (Type_error { expected; received })

let get_bool (Lit lit : value) =
  match lit with
  | Bool b -> b
  | other ->
     let expected, received = Bool, litteral_type other in
     raise (Type_error { expected; received })

let instruction conf =
  if conf.pc >= Array.length conf.program
  then Stop
  else conf.program.(conf.pc)

let reduce conf =
  let eval conf e = eval conf.heap conf.env e in
  let resolve label = Instr.resolve conf.program label in
  let pc' = conf.pc + 1 in
  assert (conf.status = Running);
  match instruction conf with
  | Comment _ -> { conf with
                   pc = pc' }
  | Stop -> { conf with
              status = Stopped }
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
     { conf with pc = resolve (if b then l1 else l2) }
  | Label _ -> { conf with pc = pc' }
  | Goto label -> { conf with pc = resolve label }
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
         pc = resolve l;
         env = new_env }
     end

let start program pc = {
  trace = [];
  heap = Heap.empty;
  env = Env.empty;
  status = Running;
  program;
  pc;
}

let stop conf =
  conf.status = Stopped

let rec reduce_bounded (conf, n) =
  if n = 0 then conf
  else let conf = reduce conf in
    reduce_bounded (conf, n - 1)

let run_bounded (prog, n) =
  let conf = start prog 0 in
    reduce_bounded (conf, n)

let rec reduce_forever conf =
  if stop conf then conf
  else reduce_forever (reduce conf)

let run_forever program =
  reduce_forever (start program 0)

let read_trace conf = List.rev conf.trace

let rec reduce_interactive conf =
  if stop conf then conf
  else begin
    let conf = reduce conf in
    let string_of_val : value -> string = function
      | Lit Nil -> "nil"
      | Lit (Bool b) -> string_of_bool b
      | Lit (Int n) -> string_of_int n in
    begin match conf.trace with
      | [] -> ()
      | vs -> print_endline (String.concat " " (List.map string_of_val vs))
    end;
    reduce_interactive { conf with trace = [] }
  end

let run_interactive program =
  reduce_interactive (start program 0)
