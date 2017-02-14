open Instr

let pcs (instrs : instruction_stream) : pc array =
  Array.mapi (fun pc _ -> pc) instrs

module PcSet = Set.Make(Pc)

let successors_at (instrs : instruction_stream) pc : pc list =
  let pc' = pc + 1 in
  let instr = instrs.(pc) in
  let resolve = Instr.resolve instrs in
  let all_succ =
    match instr with
    | Decl_const _ | Decl_mut _ | Assign _ | Drop _ | Clear _ | Read _
    | Label _ | Comment _ | Osr _ | Print _ ->
      let is_last = pc' = Array.length instrs in
      if is_last then [] else [pc']
    (* those are the instructions which manipulate controlflow:  *)
    | Stop -> []
    | Goto l -> [resolve l]
    | Branch (_e, l1, l2) -> [resolve l1; resolve l2]
  in
  PcSet.elements (PcSet.of_list all_succ)

let successors (instrs : instruction_stream) : pc list array =
  let succs_at pc = successors_at instrs pc in
  Array.map succs_at (pcs instrs)

let predecessors (instrs : instruction_stream) : pc list array =
  let preds = Array.map (fun _ -> []) instrs in
  let mark_successor pc pc' =
    preds.(pc') <- pc :: preds.(pc') in
  for pc = 0 to Array.length instrs - 1 do
    List.iter (mark_successor pc) (successors_at instrs pc)
  done;
  preds

let starts (instrs : instruction_stream) = [0]

let stops (instrs : instruction_stream) =
  let succs = successors instrs in
  let is_exit pc = succs.(pc) = [] in
  let pcs = Array.to_list (pcs instrs) in
  List.filter is_exit pcs

let dataflow_analysis (next : pc list array)
                      (init_state : ('a * pc) list)
                      (instrs : segment)
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

let forward_analysis init_state seg merge update =
  let successors = successors seg in
  let starts = starts seg in
  assert (starts != []);
  let init = List.map (fun pos -> (init_state, pos)) starts in
  make_total (dataflow_analysis successors init seg merge update)

let backwards_analysis init_state instrs merge update =
  let predecessors = predecessors instrs in
  let stops = stops instrs in
  assert (stops != []);
  let init = List.map (fun pos -> (init_state, pos)) stops in
  make_total (dataflow_analysis predecessors init instrs merge update)


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
    let merge_one _ a b : PcSet.t option =
      match a, b with
      | None, None -> None
      | Some a, None -> Some a
      | None, Some b -> Some b
      | Some a, Some b -> Some (PcSet.union a b) in
    merge merge_one

  let singleton var loc =
      add var (PcSet.singleton loc) empty

  let equal =
    let is_equal a b = PcSet.equal a b in
    equal is_equal

  let at var this =
    match find var this with
    | v -> v
    | exception Not_found -> PcSet.empty
end

(* returns a 'pc -> pc set' computing reaching definitions *)
let reaching (instrs : segment) : pc -> PcSet.t =
  let merge _pc cur_defs in_defs =
    let merged = VariableMap.union cur_defs in_defs in
    if VariableMap.equal cur_defs merged then None else Some merged
  in
  let update pc defs =
    let instr = instrs.(pc) in
    (* add or override defined vars in one go*)
    let kill = VarSet.elements (ModedVarSet.untyped (defined_vars instr)) in
    let loc = PcSet.singleton pc in
    let replace acc var = VariableMap.add var loc acc in
    List.fold_left replace defs kill
  in
  let res = forward_analysis VariableMap.empty instrs merge update in
  fun pc ->
    let instr = instrs.(pc) in
    let used = VarSet.elements (used_vars instr) in
    let definitions_of var = VariableMap.find var (res pc) in
    let all_definitions = List.map definitions_of used in
    List.fold_left PcSet.union PcSet.empty all_definitions


let liveness_analysis (instrs : segment) =
  let merge _pc cur_uses in_uses =
    let merged = VariableMap.union cur_uses in_uses in
    if VariableMap.equal cur_uses merged then None else Some merged
  in
  let update pc uses =
    let instr = instrs.(pc) in
    (* First remove defined vars *)
    let kill = VarSet.elements (ModedVarSet.untyped (defined_vars instr)) in
    let remove acc var = VariableMap.remove var acc in
    let uses = List.fold_left remove uses kill in
    (* Then add used vars *)
    let used = VarSet.elements (used_vars instr) in
    let merge acc var = VariableMap.union (VariableMap.singleton var pc) acc
    in
    List.fold_left merge uses used
  in
  backwards_analysis VariableMap.empty instrs merge update


(* returns a 'pc -> variable set' computing live vars at a certain pc *)
let live (seg : segment) : pc -> variable list =
  let res = liveness_analysis seg in
  fun pc ->
    let collect_key (key, value) = key in
    let live_vars = List.map collect_key (VariableMap.bindings (res pc)) in
    live_vars

(* returns a 'pc -> pc set' computing uses of a definition *)
let used (instrs : segment) : pc -> PcSet.t =
  let res = liveness_analysis instrs in
  fun pc ->
    let instr = instrs.(pc) in
      let defined = VarSet.elements (ModedVarSet.untyped (defined_vars instr)) in
      let uses_of var = VariableMap.at var (res pc) in
      let all_uses = List.map uses_of defined in
      List.fold_left PcSet.union PcSet.empty all_uses
