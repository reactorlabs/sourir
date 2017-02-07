open Instr

module Env = Map.Make(Variable)
module Heap = Map.Make(Address)

type input = IO.input
type trace = value list
type environment = binding Env.t
type heap = heap_value Heap.t

type status = Running | Stopped

type configuration = {
  input : input;
  trace : trace;
  heap : heap;
  env : environment;
  program : program_;
  instrs : instruction_stream;
  pc : pc;
  status : status;
  deopt : string option;
}

type litteral_type = Nil | Bool | Int
let litteral_type : litteral -> litteral_type = function
  | Nil -> Nil
  | Bool _ -> Bool
  | Int _ -> Int

exception Unbound_variable of variable
exception Undefined_variable of variable
exception Invalid_heap
exception Arity_error of primop
exception Invalid_update
exception Invalid_clear

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
    | Undefined -> raise (Undefined_variable x)
    | Value v -> v
    end

let update heap env x v =
  match Env.find x env with
  | exception Not_found -> raise (Unbound_variable x)
  | Const _ -> raise Invalid_update
  | Mut a ->
    begin match Heap.find a heap with
    | exception Not_found -> raise Invalid_heap
    | _ -> Heap.add a (Value v) heap
    end

let drop heap env x =
  match Env.find x env with
  | exception Not_found -> raise (Unbound_variable x)
  | Const _ -> (heap, Env.remove x env)
  | Mut a -> (Heap.remove a heap, Env.remove x env)

let clear heap env x =
  match Env.find x env with
  | exception Not_found -> raise (Unbound_variable x)
  | Const _ -> raise Invalid_clear
  | Mut a -> Heap.add a Undefined heap

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
  | (Int _ | Nil | Bool _) as x1, x2 ->
      let expected = (Int, Int) in
      let received = litteral_type x1, litteral_type x2 in
      raise (ProductType_error { expected; received })


let value_eq (Lit lit1) (Lit lit2) = litteral_eq lit1 lit2
let value_neq (Lit lit1) (Lit lit2) = not (litteral_eq lit1 lit2)
let value_plus (Lit lit1) (Lit lit2) = litteral_plus lit1 lit2

let eval_simple heap env = function
  | Var x -> lookup heap env x
  | Lit lit -> Lit lit

let rec eval heap env = function
  | Simple e -> eval_simple heap env e
  | Op (op, es) ->
    begin match op, List.map (eval_simple heap env) es with
    | Eq, [v1; v2] -> Lit (Bool (value_eq v1 v2))
    | Neq, [v1; v2] -> Lit (Bool (value_neq v1 v2))
    | Plus, [v1; v2] -> Lit (Int (value_plus v1 v2))
    | (Eq | Neq | Plus), _vs -> raise (Arity_error op)
    end

let get_int (Lit lit : value) =
  match lit with
  | Int n -> n
  | (Nil | Bool _) as other ->
     let expected, received = Int, litteral_type other in
     raise (Type_error { expected; received })

let get_bool (Lit lit : value) =
  match lit with
  | Bool b -> b
  | (Nil | Int _) as other ->
     let expected, received = Bool, litteral_type other in
     raise (Type_error { expected; received })

let instruction conf =
  if conf.pc >= Array.length conf.instrs
  then Stop
  else conf.instrs.(conf.pc)

let reduce conf =
  let eval conf e = eval conf.heap conf.env e in
  let resolve instrs label = Instr.resolve instrs label in
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
  | Decl_mut (x, Some e) ->
     let a = Address.fresh () in
     let v = eval conf e in
     { conf with
       heap = Heap.add a (Value v) conf.heap;
       env = Env.add x (Mut a) conf.env;
       pc = pc';
     }
  | Decl_mut (x, None) ->
     let a = Address.fresh () in
     { conf with
       heap = Heap.add a Undefined conf.heap;
       env = Env.add x (Mut a) conf.env;
       pc = pc';
     }
  | Drop x ->
    let (heap, env) = drop conf.heap conf.env x in
    { conf with
      heap; env;
      pc = pc';
    }
  | Clear x ->
    let heap = clear conf.heap conf.env x in
    { conf with
      heap;
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
     { conf with pc = resolve conf.instrs (if b then l1 else l2) }
  | Label _ -> { conf with pc = pc' }
  | Goto label -> { conf with pc = resolve conf.instrs label }
  | Read x ->
    let (IO.Next (v, input')) = conf.input () in
    { conf with
      heap = update conf.heap conf.env x v;
      input = input';
      pc = pc';
    }
  | Print e ->
     let v = eval conf e in
     { conf with
       trace = v :: conf.trace;
       pc = pc';
     }
  | Osr (e, v, l, osr) ->
     let b = get_bool (eval conf e) in
     if not b then
       { conf with
         pc = pc';
       }
     else begin
       let add (env, heap) = function
         | OsrConst (x, e) ->
           (Env.add x (Const (eval conf e)) env,
            heap)
         | OsrMut (x, OsrExp e) ->
           let a = Address.fresh () in
           (Env.add x (Mut a) env,
            Heap.add a (Value (eval conf e)) heap)
         | OsrMut (x, OsrUndef) ->
           let a = Address.fresh () in
           (Env.add x (Mut a) env,
            Heap.add a Undefined conf.heap)
       in
       let (env', heap') = List.fold_left add (Env.empty, conf.heap) osr in
       let instrs = fst (List.assoc v conf.program) in
       { conf with
         pc = resolve instrs l;
         env = env';
         heap = heap';
         instrs = instrs;
         deopt = Some l;
       }
     end

let start program input pc : configuration = {
  input;
  trace = [];
  heap = Heap.empty;
  env = Env.empty;
  status = Running;
  deopt = None;
  program = program;
  instrs = fst (List.assoc "main" program);
  pc;
}

let stop conf =
  conf.status = Stopped

let rec reduce_bounded (conf, n) =
  if n = 0 then conf
  else let conf = reduce conf in
    reduce_bounded (conf, n - 1)

let run_bounded input (prog, n) =
  let conf = start prog input 0 in
    reduce_bounded (conf, n)

let rec reduce_forever conf =
  if stop conf then conf
  else reduce_forever (reduce conf)

let run_forever input (program : program_) =
  reduce_forever (start program input 0)

let read_trace conf = List.rev conf.trace

let rec reduce_interactive conf =
  if stop conf then conf
  else begin
    let conf = reduce conf in
    begin match conf.trace with
      | [] -> ()
      | vs -> print_endline (String.concat " " (List.map string_of_value vs))
    end;
    reduce_interactive { conf with trace = [] }
  end

let run_interactive input program =
  reduce_interactive (start program input 0)
