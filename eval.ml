open Instr

module Env = Map.Make(Variable)
module Heap = Map.Make(Address)

type input = IO.input
type trace = string list
type environment = binding Env.t
type heap = heap_value Heap.t

type status = Running | Result of value
type position = identifier * label * pc
type continuation = variable * environment * position

type configuration = {
  input : input;
  trace : trace;
  heap : heap;
  env : environment;
  program : program;
  pc : pc;
  cur_fun : identifier;
  cur_vers : label;
  instrs : instruction_stream;
  status : status;
  deopt : string option;
  continuation : continuation list;
}

type value_type = Nil | Bool | Int | FunRef
let value_type : value -> value_type = function
  | Nil -> Nil
  | Bool _ -> Bool
  | Int _ -> Int
  | FunRef _ -> FunRef

exception Unbound_variable of variable
exception Undefined_variable of variable
exception Invalid_heap
exception Arity_error of primop
exception Invalid_update
exception Invalid_clear

type type_error = {
  expected : value_type;
  received : value_type;
}
exception Type_error of type_error
type product_type_error = {
  expected : value_type * value_type;
  received : value_type * value_type;
}
exception ProductType_error of product_type_error

let lookup heap env x =
  match Env.find x env with
  | exception Not_found -> raise (Unbound_variable x)
  | Val v -> v
  | Ref a ->
    begin match Heap.find a heap with
    | exception Not_found -> raise Invalid_heap
    | Undefined -> raise (Undefined_variable x)
    | Value v -> v
    end

let update heap env x v =
  match Env.find x env with
  | exception Not_found -> raise (Unbound_variable x)
  | Val _ -> raise Invalid_update
  | Ref a ->
    begin match Heap.find a heap with
    | exception Not_found -> raise Invalid_heap
    | _ -> Heap.add a (Value v) heap
    end

let drop heap env x =
  match Env.find x env with
  | exception Not_found -> raise (Unbound_variable x)
  | Val _ -> (heap, Env.remove x env)
  | Ref a -> (Heap.remove a heap, Env.remove x env)

let clear heap env x =
  match Env.find x env with
  | exception Not_found -> raise (Unbound_variable x)
  | Val _ -> raise Invalid_clear
  | Ref a -> Heap.add a Undefined heap

let value_eq (v1 : value) (v2 : value) =
  match v1, v2 with
  | Nil, Nil -> true
  | Nil, _ | _, Nil -> false
  | Bool b1, Bool b2 -> b1 = b2
  | Bool _, _ | _, Bool _ -> false
  | Int n1, Int n2 -> n1 = n2
  | Int _, _ | _, Int _ -> false
  | FunRef f1, FunRef f2 -> f1 = f2

let value_plus (v1 : value) (v2 : value) =
  match v1, v2 with
  | Int n1, Int n2 -> n1 + n2
  | (Int _ | Nil | Bool _ | FunRef _) as x1, x2 ->
      let expected = (Int, Int) in
      let received = value_type x1, value_type x2 in
      raise (ProductType_error { expected; received })

let value_neq (v1 : value) (v2 : value) =
  not (value_eq v1 v2)

let eval_simple prog heap env = function
  | Var x -> lookup heap env x
  | Lit (FunRef f) -> FunRef (lookup_fun prog f)
  | Lit (Int i) -> Int i
  | Lit (Bool b) -> Bool b
  | Lit Nil -> Nil

let rec eval prog heap env = function
  | Simple e -> eval_simple prog heap env e
  | Op (op, es) ->
    begin match op, List.map (eval_simple prog heap env) es with
    | Eq, [v1; v2] -> Bool (value_eq v1 v2)
    | Neq, [v1; v2] -> Bool (value_neq v1 v2)
    | Plus, [v1; v2] -> Int (value_plus v1 v2)
    | (Eq | Neq | Plus), _vs -> raise (Arity_error op)
    end

let get_bool (v : value) =
  match v with
  | Bool b -> b
  | (Nil | Int _ | FunRef _) as other ->
     let expected, received = Bool, value_type other in
     raise (Type_error { expected; received })

let get_fun (v : value) =
  match v with
  | FunRef f -> f
  | (Nil | Int _ | Bool _) as other ->
     let expected, received = FunRef, value_type other in
     raise (Type_error { expected; received })

exception InvalidArgument
exception InvalidNumArgs

let reduce conf =
  let eval conf e = eval conf.program conf.heap conf.env e in
  let resolve instrs label = Instr.resolve instrs label in
  let pc' = conf.pc + 1 in
  assert (conf.status = Running);

  let instruction =
    let default_exit = (Simple (Lit (Int 0))) in
    if conf.pc < Array.length conf.instrs
    then conf.instrs.(conf.pc)
    else if conf.continuation = []
    then Stop default_exit
    else assert (false)
  in

  let build_call_frame formals actuals =
    let eval_arg env (formal, actual) =
      match[@warning "-4"] formal, actual with
      | Instr.Const_val_param x, Arg_by_val e ->
        let value = eval conf e in
        Env.add x (Val value) env
      | Instr.Mut_ref_param x, Arg_by_ref var ->
        let get_addr = function
          | Ref a as adr -> adr
          | Val _ -> raise InvalidArgument
        in
        let adr = get_addr (Env.find var conf.env) in
        Env.add x adr env
      | _ -> raise InvalidArgument
    in
    let args = List.combine formals actuals in
    List.fold_left eval_arg Env.empty args
  in

  let build_osr_frame osr_def =
    let add env' = function
      | Osr_const (x', e) ->
        Env.add x' (Val (eval conf e)) env'
      | Osr_mut (x', x) ->
        begin match Env.find x conf.env with
        | exception Not_found -> raise (Unbound_variable x)
        | Val _ -> raise Invalid_heap
        | Ref a -> Env.add x' (Ref a) env'
        end
      | Osr_mut_undef x' ->
        let a = Address.fresh () in
        Env.add x' (Ref a) env'
    in
    List.fold_left add Env.empty osr_def
  in

  match instruction with
  | StaticCall (x, f, args) ->
    let func = Instr.lookup_fun conf.program f in
    let version = Instr.active_version func in
    let call_env = build_call_frame func.formals args in
    let cont_pos = (conf.cur_fun, conf.cur_vers, pc') in
    { conf with
      env = call_env;
      instrs = version.instrs;
      pc = 0;
      cur_fun = func.name;
      cur_vers = version.label;
      continuation = (x, conf.env, cont_pos) :: conf.continuation
    }
  | Call (x, f, args) ->
    let func = get_fun(eval conf f) in
    if List.length func.formals <> List.length args then raise InvalidNumArgs;
    let version = Instr.active_version func in
    let call_env = build_call_frame func.formals args in
    let cont_pos = (conf.cur_fun, conf.cur_vers, pc') in
    { conf with
      env = call_env;
      instrs = version.instrs;
      pc = 0;
      cur_fun = func.name;
      cur_vers = version.label;
      continuation = (x, conf.env, cont_pos) :: conf.continuation
    }
  | Return e ->
     let res = eval conf e in
     begin match conf.continuation with
     | [] ->
       { conf with
         status = Result res }
     | (x, env, (f, v, pc)) :: cont ->
       let env = Env.add x (Val res) env in
       let func = Instr.lookup_fun conf.program f in
       let version = Instr.get_version func v in
       { conf with
         env = env;
         cur_fun = func.name;
         cur_vers = version.label;
         instrs = version.instrs;
         pc = pc;
         continuation = cont; }
     end
  | Stop e ->
     let v = eval conf e in
     { conf with
       status = Result v }
  | Comment _ -> { conf with
                   pc = pc' }
  | Decl_const (x, e) ->
     let v = eval conf e in
     { conf with
       env = Env.add x (Val v) conf.env;
       pc = pc';
     }
  | Decl_mut (x, Some e) ->
     let a = Address.fresh () in
     let v = eval conf e in
     { conf with
       heap = Heap.add a (Value v) conf.heap;
       env = Env.add x (Ref a) conf.env;
       pc = pc';
     }
  | Decl_mut (x, None) ->
     let a = Address.fresh () in
     { conf with
       heap = Heap.add a Undefined conf.heap;
       env = Env.add x (Ref a) conf.env;
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
       trace = (string_of_value v) :: conf.trace;
       pc = pc';
     }
  | Osr (e, f, v, l, osr_def) ->
     let b = get_bool (eval conf e) in
     if not b then
       { conf with
         pc = pc';
       }
     else begin
       let osr_env = build_osr_frame osr_def in
       let osr_func = Instr.lookup_fun conf.program f in
       let osr_version = Instr.get_version osr_func v in
       let osr_instrs = osr_version.instrs in
       { conf with
         pc = resolve osr_instrs l;
         env = osr_env;
         instrs = osr_instrs;
         cur_fun = osr_func.name;
         cur_vers = osr_version.label;
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
  cur_fun = "main";
  cur_vers = (Instr.active_version program.main).label;
  instrs = (Instr.active_version program.main).instrs;
  pc = pc;
  continuation = []
}

let stop conf =
  match conf.status with
  | Running -> false
  | Result _ -> true

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

let run_forever input (program : program) =
  reduce_forever (start program input 0)

let read_trace conf = List.rev conf.trace

let rec reduce_interactive conf =
  if stop conf then conf
  else begin
    let conf = reduce conf in
    begin match conf.trace with
      | [] -> ()
      | vs -> print_endline (String.concat " " vs)
    end;
    reduce_interactive { conf with trace = [] }
  end

let run_interactive input program =
  reduce_interactive (start program input 0)
