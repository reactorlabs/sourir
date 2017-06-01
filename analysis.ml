open Instr
open Types

let pcs (instrs : instructions) : pc array =
  Array.mapi (fun pc _ -> pc) instrs

type position =
  | Arg
  | Instr of pc

module Position = struct
  type t = position
  let compare (x : position) (y : position) =
    match x, y with
    | Arg, Arg -> 0
    | Arg, _ -> -1
    | _, Arg -> 1
    | Instr x, Instr y -> Pervasives.compare x y
end

module PcSet = Set.Make(Pc)
module PosSet = Set.Make(Position)

let successors_at (instrs : instructions) pc : pc list =
  let pc' = pc + 1 in
  let instr = instrs.(pc) in
  let resolve = Instr.resolve instrs in
  let all_succ =
    match instr with
    | Decl_var _ | Decl_array _
    | Assign _ | Array_assign _
    | Drop _ | Read _ | Call _ | Label _
    | Comment _ | Osr _ | Print _ | Assert _ ->
      let is_last = pc' = Array.length instrs in
      if is_last then [] else [pc']
    (* those are the instructions which manipulate controlflow:  *)
    | Stop _ | Return _ -> []
    | Goto l -> [resolve (MergeLabel l)]
    | Branch (_e, l1, l2) ->
        [resolve (BranchLabel l1); resolve (BranchLabel l2)]
  in
  PcSet.elements (PcSet.of_list all_succ)

let successors (instrs : instructions) : pc list array =
  let succs_at pc = successors_at instrs pc in
  Array.map succs_at (pcs instrs)

let predecessors (instrs : instructions) : pc list array =
  let preds = Array.map (fun _ -> []) instrs in
  let mark_successor pc pc' =
    preds.(pc') <- pc :: preds.(pc') in
  for pc = 0 to Array.length instrs - 1 do
    List.iter (mark_successor pc) (successors_at instrs pc)
  done;
  assert (Array.length instrs = Array.length preds);
  preds

let starts (instrs : instructions) = [0]

let stops (instrs : instructions) =
  let succs = successors instrs in
  let is_exit pc = succs.(pc) = [] in
  let pcs = Array.to_list (pcs instrs) in
  List.filter is_exit pcs

let osrs (instrs : instructions) =
  let is_osr pc = match[@warning "-4"] instrs.(pc) with
    | Osr _ -> true
    | _ -> false in
  let pcs = Array.to_list (pcs instrs) in
  List.filter is_osr pcs

let dataflow_analysis (next : pc list array)
                      (init_state : ('a * pc) list)
                      (instrs : instructions)
                      (merge : pc -> 'a -> 'a -> 'a option)
                      (update : pc -> 'a -> 'a)
                      : 'a option array =
  if Array.length instrs == 0 then [||] else
  let program_state = Array.map (fun _ -> None) instrs in
  let rec work = function
    | [] -> ()
    | (in_state, pc) :: rest ->
        let merged =
          match program_state.(pc) with
          | None -> Some in_state
          | Some cur_state -> merge pc cur_state in_state
        in begin match merged with
        | None -> work rest
        | Some new_state ->
            program_state.(pc) <- merged;
            let updated = update pc new_state in
            let continue = next.(pc) in
            let new_work = List.map (fun pc' -> (updated, pc')) continue in
            work (new_work @ rest)
        end
  in
  work init_state;
  program_state

exception UnreachableCode of pc

let make_total result =
  fun pc ->
    match result.(pc) with
    | None -> raise (UnreachableCode pc)
    | Some res -> res

let forward_analysis init_state instrs merge update =
  let successors = successors instrs in
  let starts = starts instrs in
  assert (starts <> []);
  let init = List.map (fun pos -> (init_state, pos)) starts in
  make_total (dataflow_analysis successors init instrs merge update)

let backwards_analysis init_state instrs merge update =
  let predecessors = predecessors instrs in
  let exits = stops instrs @ osrs instrs in
  assert (exits <> []);
  let init = List.map (fun pos -> (init_state, pos)) exits in
  make_total (dataflow_analysis predecessors init instrs merge update)

let find (next : pc list array)
         (start : pc)
         (instrs : instructions)
         (predicate : pc -> bool) : pc =
  let rec work todo seen =
    match todo with
    | [] -> raise Not_found
    | pc :: rest when PcSet.mem pc seen ->
      work rest seen    (* already checked *)
    | pc :: rest when predicate pc ->
      pc                (* fits predicate *)
    | pc :: rest ->
      let seen, todo = PcSet.add pc seen, next.(pc) @ todo in
      work todo seen    (* schedule next *)
  in
  work [start] PcSet.empty

let find_first (instrs : instructions)
               (predicate : pc -> bool) : pc =
  let succ = successors instrs in
  find succ 0 instrs predicate

(* Use - Def style analysis *)

(* [Analysis result] Map: variable -> pc set
 *
 * Is used to represent the eg. the set of instructions
 * defining a certain variable *)
module VariableMap = struct
  include Map.Make(Variable)
  module KeySet = Set.Make(Variable)

  (* merge is defined as the union of their equally named sets *)
  let union =
    let merge_one _ a b : PosSet.t option =
      match a, b with
      | None, None -> None
      | Some a, None -> Some a
      | None, Some b -> Some b
      | Some a, Some b -> Some (PosSet.union a b) in
    merge merge_one

  let singleton var loc =
    add var (PosSet.singleton loc) empty

  let initial vars =
    List.fold_left (fun s x -> union s (singleton x Arg)) empty vars

  let equal =
    let is_equal a b = PosSet.equal a b in
    equal is_equal

  let at var this =
    match find var this with
    | v -> v
    | exception Not_found -> PosSet.empty
end

exception DuplicateFormalParameter

let as_var_set (formals : formal_parameter list) =
  let to_var (Param x) = x in
  let formals' = VarSet.of_list (List.map to_var formals) in
  if (List.length formals) <> (List.length (VarSet.elements formals')) then
    raise DuplicateFormalParameter;
  formals'

let as_var_map formals =
  let formals = VarSet.elements formals in
  VariableMap.initial formals

let as_analysis_input (func:afunction) (version:version) =
  { formals = as_var_set func.formals; instrs = version.instrs }

(* returns a 'pc -> pc set' computing reaching definitions *)
let reaching {formals; instrs} : pc -> PosSet.t =
  let merge _pc cur_defs in_defs =
    let merged = VariableMap.union cur_defs in_defs in
    if VariableMap.equal cur_defs merged then None else Some merged
  in
  let update pc defs =
    let instr = instrs.(pc) in
    (* add or override defined vars in one go*)
    let kill = defined_vars instr in
    let loc = PosSet.singleton (Instr pc) in
    let replace var acc = VariableMap.add var loc acc in
    VarSet.fold replace kill defs
  in
  let res = forward_analysis (as_var_map formals) instrs merge update in
  fun pc ->
    let instr = instrs.(pc) in
    let used = VarSet.elements (used_vars instr) in
    let definitions_of var = VariableMap.find var (res pc) in
    let all_definitions = List.map definitions_of used in
    List.fold_left PosSet.union PosSet.empty all_definitions

let scope_analysis (introduction : instruction -> variable list)
                   (elimination : instruction -> variable list)
                   ({formals; instrs} : analysis_input) =
  let merge _pc cur_scope in_scope =
    let merged = VariableMap.union cur_scope in_scope in
    if VariableMap.equal cur_scope merged then None else Some merged
  in
  let update pc cur_scope =
    let instr = instrs.(pc) in
    let to_remove = introduction instr in
    let cur_scope = List.fold_right VariableMap.remove to_remove cur_scope in
    let to_add = elimination instr in
    let entry var = VariableMap.singleton var (Instr pc) in
    let merge acc var = VariableMap.union (entry var) acc in
    List.fold_left merge cur_scope to_add
  in
  backwards_analysis VariableMap.empty instrs merge update

let liveness_analysis ({instrs} as inp : analysis_input) =
  let introduction instr = VarSet.elements (defined_vars instr) in
  let elimination instr = VarSet.elements (used_vars instr) in
  scope_analysis introduction elimination inp

let lifetime_analysis ({instrs} as inp : analysis_input) =
  let introduction instr = VarSet.elements (declared_vars instr) in
  let elimination instr = VarSet.elements (required_vars instr) in
  scope_analysis introduction elimination inp

(* returns a 'pc -> variable set' computing live vars at a certain pc *)
let live (inp : analysis_input) : pc -> variable list =
  let res = liveness_analysis inp in
  fun pc ->
    let collect_key (key, value) = key in
    let live_vars = List.map collect_key (VariableMap.bindings (res pc)) in
    live_vars

let as_pc_set pos_set =
  let pos = PosSet.elements pos_set in
  let pos = List.map (fun p -> match p with
      | Arg -> assert (false)
      | Instr p -> p) pos in
  PcSet.of_list pos

(* returns a 'pc -> pc set' computing uses of a definition *)
let uses ({instrs} as inp : analysis_input) : pc -> PcSet.t =
  let res = liveness_analysis inp in
  fun pc ->
    let add_uses x used = PosSet.union used (VariableMap.at x (res pc)) in
    let pos = VarSet.fold add_uses (defined_vars instrs.(pc)) PosSet.empty in
    (* formal parameter cannot be an use *)
    as_pc_set pos

let dominates ({instrs} : analysis_input) : pc -> pc -> bool =
  let merge _pc cur incom =
    let merged = PosSet.inter cur incom in
    if PosSet.equal merged cur then None else Some merged
  in
  let update pc cur =
    PosSet.add (Instr pc) cur
  in
  let dominators = forward_analysis PosSet.empty instrs merge update in
  fun pc pc' ->
    let doms = dominators pc' in
    PosSet.mem (Instr pc) doms

(* returns a 'pc -> pc set' computing the set of instructions depending on a declaration *)
let required ({instrs} as inp : analysis_input) : pc -> PcSet.t =
  let res = lifetime_analysis inp in
  fun pc ->
    let add_uses x used = PosSet.union used (VariableMap.at x (res pc)) in
    let pos = VarSet.fold add_uses (declared_vars instrs.(pc)) PosSet.empty in
    (* formal parameter cannot be a require *)
    as_pc_set pos

(* returns a 'pc -> variable set' computing variables which need to be in scope
 * Note: they might not be! *)
let required_vars ({instrs} as inp : analysis_input) : pc -> variable list =
  let res = lifetime_analysis inp in
  fun pc -> List.map fst (VariableMap.bindings (res pc))

let aliased ({formals; instrs} : analysis_input) : pc -> VarSet.t =
  let ref_param params x = x :: params in
  let mut_formals = List.fold_left ref_param [] (VarSet.elements formals) in
  fun _ -> VarSet.of_list mut_formals

module Expression = struct
  type t = expression
  let compare (x : expression) (y : expression) =
    Pervasives.compare x y
end

module ExpressionSet = Set.Make(Expression)

let valid_assumptions {instrs} : pc -> ExpressionSet.t =
  let merge _pc cur incom =
    let merged = ExpressionSet.inter cur incom in
    if ExpressionSet.equal merged cur then None else Some merged
  in
  let update pc cur =
    match[@warning "-4"] instrs.(pc) with
    | Osr {cond} ->
      List.fold_right ExpressionSet.add cond cur
    | _ ->
      ExpressionSet.filter (fun exp ->
          Instr.independent instrs.(pc) exp) cur
  in
  forward_analysis ExpressionSet.empty instrs merge update
