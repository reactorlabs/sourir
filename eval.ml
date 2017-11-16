open Instr

module Env = Map.Make(Variable)
module Heap = Map.Make(Address)

type dumped_value =
  | Nil
  | Bool of bool
  | Int of int
  | String of string
  | Fun_ref of string
  | Array of dumped_value array

type input = IO.input
type trace = dumped_value list
type environment = binding Env.t
type heap = heap_value Heap.t

type status = Running | Result of value
type continuation = variable * environment * pc position

type configuration = {
  input : input;
  trace : trace;
  heap : heap;
  env : environment;
  program : program;
  pc : pc;
  cur_fun : identifier;
  cur_vers : label;
  instrs : instructions;
  status : status;
  deopt : string option;
  continuation : continuation list;
}

type type_tag = Nil | Bool | Int | Fun_ref | Array | String
let get_tag : value -> type_tag = function
  | Nil -> Nil
  | String _ -> String
  | Bool _ -> Bool
  | Int _ -> Int
  | Fun_ref _ -> Fun_ref
  | Array _ -> Array

exception Unbound_variable of variable
exception Undefined_variable of variable
exception Invalid_heap
exception Division_by_zero
exception User_assert_failure of pc position

type type_error = {
  expected : type_tag;
  received : type_tag;
}
exception Type_error of type_error
type product_type_error = {
  expected : type_tag * type_tag;
  received : type_tag * type_tag;
}
exception Product_type_error of product_type_error

let position conf =
  {
    func = conf.cur_fun;
    version = conf.cur_vers;
    pos = conf.pc;
  }

let move_to_position pos conf =
  let func = Instr.lookup_fun conf.program pos.func in
  let version = Instr.get_version func pos.version in
  { conf with
    cur_fun = func.name;
    cur_vers = version.label;
    instrs = version.instrs;
    pc = pos.pos;
  }

let lookup heap env x =
  match Env.find x env with
  | exception Not_found -> raise (Unbound_variable x)
  | Val v -> v
  | Ref a ->
    begin match Heap.find a heap with
    | exception Not_found -> raise Invalid_heap
    | Undefined -> raise (Undefined_variable x)
    | Value v -> v
    | Block _ -> raise Invalid_heap
    end

let update heap env x v =
  match Env.find x env with
  | exception Not_found -> raise (Unbound_variable x)
  | Val _ -> heap, Env.add x (Val v) env
  | Ref a ->
    begin match Heap.find a heap with
    | exception Not_found -> raise Invalid_heap
    | _ -> Heap.add a (Value v) heap, env
    end

let drop heap env x =
  match Env.find x env with
  | exception Not_found -> raise (Unbound_variable x)
  | Val _ -> (heap, Env.remove x env)
  | Ref a -> (Heap.remove a heap, Env.remove x env)

let rec dump_value heap : value -> dumped_value = function
  | Nil -> Nil
  | String s -> String s
  | Bool b -> Bool b
  | Int n -> Int n
  | Fun_ref f -> Fun_ref f
  | Array a ->
    begin match Heap.find a heap with
    | exception Not_found -> raise Invalid_heap
    | Undefined -> raise Invalid_heap
    | Value v -> dump_value heap v
    | Block vs -> (Array
        (Array.map (dump_value heap) vs))
    end

let rec string_of_dumped_value : dumped_value -> string = function
  | Nil -> "nil"
  | String s -> Printf.sprintf "\"%s\"" s
  | Bool b -> string_of_bool b
  | Int n -> string_of_int n
  | Fun_ref f -> Printf.sprintf "'%s" f
  | Array vs ->
      Printf.sprintf "[%s]"
        (String.concat ", "
         (List.map string_of_dumped_value (Array.to_list vs)))

let rec value_eq (v1 : value) (v2 : value) =
  match v1, v2 with
  | Nil, Nil -> true
  | Nil, _ | _, Nil -> false
  | Bool b1, Bool b2 -> b1 = b2
  | Bool _, _ | _, Bool _ -> false
  | Int n1, Int n2 -> n1 = n2
  | Int _, _ | _, Int _ -> false
  | Fun_ref f1, Fun_ref f2 -> f1 = f2
  | Fun_ref _, _ | _, Fun_ref _ -> false
  | String a, String b -> a = b
  | String _, _ | _, String _ -> false
  | Array addr1, Array addr2 -> Address.compare addr1 addr2 = 0
(*
  | Array _, _ | _, Array _ -> .
    (* The case above cannot happen. If you add a new constructor,
       this line may need to return "false" and you can add
       a refutation clause of the same shape for the new
       constructor. *)
    (* Remark: bisect-ppx 1.2.0 has a bug that makes refutation clauses
       (p -> .) break code coverage instrumentation, so this case is
       commented out. We sent a bugfix upstream (#118). *)
*)

let get_int (v : value) =
  match v with
  | Int i -> i
  | (Nil | Bool _ | Fun_ref _ | Array _ | String _) as other ->
     let expected, received = Int, get_tag other in
     raise (Type_error { expected; received })

let get_bool (v : value) =
  match v with
  | Bool b -> b
  | (Nil | Int _ | Fun_ref _ | Array _ | String _) as other ->
     let expected, received = Bool, get_tag other in
     raise (Type_error { expected; received })

let get_fun (v : value) =
  match v with
  | Fun_ref f -> f
  | (Nil | Int _ | Bool _ | Array _ | String _) as other ->
     let expected, received = Fun_ref, get_tag other in
     raise (Type_error { expected; received })

let get_array heap (v : value) =
  match v with
  | (Nil | Int _ | Bool _ | Fun_ref _ | String _) as other ->
     let expected, received = Array, get_tag other in
     raise (Type_error { expected; received })
  | Array addr ->
    begin match Heap.find addr heap with
      | exception Not_found -> raise Invalid_heap
      | Undefined | Value _ -> raise Invalid_heap
      | Block vs -> vs
    end

let prim1 (type a) (type b) (f : a -> b) (tag, (get : value -> a)) : value -> b =
  fun v -> f (get v)

let prim2 (type a) (type b) (type c) (f : a -> b -> c)
    (taga, (geta : value -> a)) (tagb, (getb : value -> b))
  : value -> value -> c =
  fun va vb ->
    match geta va, getb vb with
    | exception _ ->
      let expected = (taga, tagb) in
      let received = (get_tag va, get_tag vb) in
      raise (Product_type_error { expected; received })
    | va, vb -> f va vb

let value_neq (v1 : value) (v2 : value) =
  not (value_eq v1 v2)

let int, bool = (Int, get_int), (Bool, get_bool)

let value_lt = prim2 (<) int int
let value_lte = prim2 (<=) int int
let value_gt = prim2 (>) int int
let value_gte = prim2 (>=) int int

let value_neg = prim1 (~-) int

let value_plus = prim2 (+) int int
let value_sub = prim2 (-) int int
let value_mult = prim2 ( * ) int int

let value_div =
  let div n1 n2 =
    if n2 = 0 then raise Division_by_zero
    else n1 / n2 in
  prim2 div int int

let value_mod =
  let modulo n1 n2 =
    if n2 = 0 then raise Division_by_zero
    else n1 mod n2
  in
  prim2 modulo int int

let value_not = prim1 not bool
let value_and = prim2 (&&) bool bool
let value_or = prim2 (||) bool bool

let eval_simple heap env = function
  | Var x -> lookup heap env x
  | Constant c -> c

let rec eval heap env = function
  | Simple e -> eval_simple heap env e
  | Binop (op, a, b) ->
    let v1, v2 = eval_simple heap env a, eval_simple heap env b in
    begin match op with
    | Eq   -> Bool (value_eq v1 v2)
    | Neq  -> Bool (value_neq v1 v2)
    | Lt   -> Bool (value_lt v1 v2)
    | Lte  -> Bool (value_lte v1 v2)
    | Gt   -> Bool (value_gt v1 v2)
    | Gte  -> Bool (value_gte v1 v2)
    | Plus -> Int (value_plus v1 v2)
    | Sub  -> Int (value_sub v1 v2)
    | Mult -> Int (value_mult v1 v2)
    | Div  -> Int (value_div v1 v2)
    | Mod  -> Int (value_mod v1 v2)
    | And  -> Bool (value_and v1 v2)
    | Or   -> Bool (value_or v1 v2)
    end
  | Unop (op, e) ->
    let v = eval_simple heap env e in
    begin match op with
    | Not -> Bool (value_not v)
    | Neg -> Int (value_neg v)
    end
  | Array_index (x, e) ->
    let a, i = lookup heap env x, eval_simple heap env e in
      let array, index = get_array heap a, get_int i in
      array.(index)
  | Array_length e ->
      let v = eval_simple heap env e in
      let array = get_array heap v in
      Int (Array.length array)

exception InvalidArgument
exception InvalidNumArgs
exception LabelFallthrough of label_type

let instruction conf =
  let default_exit = (Simple (Constant (Int 0))) in
  if conf.pc < Array.length conf.instrs
  then conf.instrs.(conf.pc)
  else if conf.continuation = []
  then Stop default_exit
  else assert (false)

let reduce conf =
  let eval conf e = eval conf.heap conf.env e in
  let resolve instrs label = Instr.resolver instrs label in
  let resolve_bailout instrs label = Instr.resolver_bailout instrs label in
  let pc' = conf.pc + 1 in
  assert (conf.status = Running);

  let build_call_frame formals actuals =
    let eval_arg env ((Param x), actual) =
      let value = eval conf actual in
      Env.add x (Val value) env
    in
    let args = List.combine formals actuals in
    List.fold_left eval_arg Env.empty args
  in

  let build_osr_frame varmap old_env old_heap =
    let add (env, heap) (x, e) =
      (Env.add x (Val (eval conf e)) env, heap)
    in
    List.fold_left add (Env.empty, old_heap) varmap
  in

  let build_extra_osr_frame (heap, frames) {cont_pos; cont_res; varmap} =
    let osr_env, heap = build_osr_frame varmap conf.env heap in
    let func = lookup_fun conf.program cont_pos.func in
    let version = get_version func cont_pos.version in
    (* osr target is a label, but continuation uses pc,
     * need to convert here: *)
    let pos = {
      func = cont_pos.func;
      version = cont_pos.version;
      pos = resolve_bailout version.instrs cont_pos.pos} in
    heap, (cont_res, osr_env, pos) :: frames
  in

  match instruction conf with
  | Call (_, x, f, args) ->
    let f = eval conf f in
    let func = lookup_fun conf.program (get_fun f) in
    if List.length func.formals <> List.length args then raise InvalidNumArgs;
    let version = Instr.active_version func in
    let call_env = build_call_frame func.formals args in
    let return_pos = position { conf with pc = pc' } in
    { conf with
      env = call_env;
      instrs = version.instrs;
      pc = 0;
      cur_fun = func.name;
      cur_vers = version.label;
      continuation = (x, conf.env, return_pos) :: conf.continuation
    }
  | Return e ->
     let res = eval conf e in
     begin match conf.continuation with
     | [] ->
       { conf with
         status = Result res }
     | (x, env, pos) :: cont ->
       move_to_position pos {
         conf with
         env = Env.add x (Val res) env;
         continuation = cont;
       }
     end
  | Stop e ->
     let v = eval conf e in
     { conf with
       status = Result v }
  | Guard_hint _
  | Comment _ -> { conf with
                   pc = pc' }
  | Decl_var (x, e) ->
     let v = eval conf e in
     { conf with
       env = Env.add x (Val v) conf.env;
       pc = pc';
     }
  | Decl_array (x, def) ->
    let a = Address.fresh () in
    let block = match def with
      | Length e ->
        let length = get_int (eval conf e) in
        Array.make length (Nil : value)
      | List es ->
        Array.of_list (List.map (eval conf) es)
    in
    { conf with
      heap = Heap.add a (Block block : heap_value) conf.heap;
      env = Env.add x (Val (Array a)) conf.env;
      pc = pc';
    }
  | Drop x ->
    let (heap, env) = drop conf.heap conf.env x in
    { conf with
      heap; env;
      pc = pc';
    }
  | Assign (x, e) ->
     let v = eval conf e in
     let heap, env = update conf.heap conf.env x v in
     { conf with env; heap;
       pc = pc';
     }
  | Array_assign (x, i, e) ->
    let vi = eval conf i in
    let ve = eval conf e in
    let arr = lookup conf.heap conf.env x in
    let vs = get_array conf.heap arr in
    vs.(get_int vi) <- ve;
    { conf with
      pc = pc';
    }
  | Branch (e, l1, l2) ->
     let b = get_bool (eval conf e) in
     { conf with pc = 1 + (resolve conf.instrs (if b then (BranchLabel l1) else (BranchLabel l2))) }
  | Label (BailoutLabel l) ->
    { conf with
      pc = pc' }
  | Label ((BranchLabel _ | MergeLabel _) as l) -> raise (LabelFallthrough l)
  | Goto label -> { conf with pc = 1 + (resolve conf.instrs (MergeLabel label)) }
  | Read x ->
    let (IO.Next (v, input')) = conf.input () in
    let heap, env = update conf.heap conf.env x v in
    { conf with heap; env;
      input = input';
      pc = pc';
    }
  | Print e ->
    let v = eval conf e in
    { conf with
      trace = (dump_value conf.heap v) :: conf.trace;
      pc = pc';
    }
  | Assert e ->
    let v = eval conf e in
    begin match get_bool v with
      | false -> raise (User_assert_failure (position conf))
      | true ->
        { conf with
          pc = pc';
        }
    end
  | Assume {guards; target={func;version; pos=label}; varmap; extra_frames} ->
    let failed = List.exists (fun guard -> not (get_bool (eval conf guard))) guards in
    if not failed then
      { conf with
        pc = pc';
      }
    else begin
      let osr_env, heap = build_osr_frame varmap conf.env conf.heap in
      let heap, extra_frames =
        List.fold_left build_extra_osr_frame (heap, []) (List.rev extra_frames) in
      let func = Instr.lookup_fun conf.program func in
      let version = Instr.get_version func version in
      let instrs = version.instrs in
      { conf with
        pc = resolve_bailout instrs label;
        env = osr_env;
        heap;
        instrs = instrs;
        cur_fun = func.name;
        cur_vers = version.label;
        deopt = Some label;
        continuation = extra_frames @ conf.continuation
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
      | vs -> print_endline (String.concat " " (List.map string_of_dumped_value vs))
    end;
    reduce_interactive { conf with trace = [] }
  end

let run_interactive input program =
  reduce_interactive (start program input 0)
