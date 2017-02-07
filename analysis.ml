open Instr

let successors (instrs : instruction_stream) pc =
  let pc' = pc + 1 in
  let next = if pc' = Array.length instrs then [] else [pc'] in
  let resolve = Instr.resolve instrs in
  match instrs.(pc) with
  | Decl_const _
  | Decl_mut _
  | Assign _
  | Drop _
  | Clear _
  | Read _
  | Label _
  | Comment _
  | Osr _
  | Print _ -> next
  | Goto l -> [resolve l]
  | Branch (_e, l1, l2) -> [resolve l1; resolve l2]
  | Stop -> []

let predecessors (instrs : instruction_stream) =
  let preds = Array.map (fun _ -> []) instrs in
  let mark_successor pc pc' =
    preds.(pc') <- pc :: preds.(pc') in
  for pc = 0 to Array.length instrs - 1 do
    List.iter (mark_successor pc) (successors instrs pc)
  done;
  preds

let dataflow_analysis (next : pc -> pc list)
                      (init_state : ('a * pc) list)
                      (seg : segment)
                      (merge : 'a -> 'a -> 'a option)
                      (update : pc -> 'a -> 'a)
                      : 'a option array =
  let instrs = fst seg in
  let program_state = Array.map (fun _ -> None) instrs in
  let rec work = function
    | [] -> ()
    | (in_state, pc) :: rest ->
        let merged =
          match program_state.(pc) with
          | None -> Some in_state
          | Some cur_state -> merge cur_state in_state
        in begin match merged with
        | None -> work rest
        | Some new_state ->
            program_state.(pc) <- merged;
            let updated = update pc new_state in
            let cont = next pc in
            let new_work = List.map (fun pc -> (updated, pc)) cont in
            work (new_work @ rest)
        end
  in
  work init_state;
  program_state

let exits (instrs : instruction_stream) =
  let rec exits pc : Pc.t list =
    if Array.length instrs = pc then []
    else
      let is_exit = successors instrs pc = [] in
      if is_exit then pc :: exits (pc + 1) else exits (pc + 1)
  in
  exits 0

let forward_analysis_from init_pos init_state seg =
  let successors pc = successors (fst seg) pc in
  dataflow_analysis successors [(init_state, init_pos)] seg

let forward_analysis init_state seg =
  forward_analysis_from 0 init_state seg

let backwards_analysis init_state seg =
  let instrs = fst seg in
  let exits = exits instrs in
  let init_state = List.map (fun pc -> (init_state, pc)) exits in
  let preds = predecessors instrs in
  let predecessors pc = preds.(pc) in
  dataflow_analysis predecessors init_state seg



(* Use - Def style analysis *)

(* a set of instructions *)
module InstrSet = Set.Make(Pc)

(* [Analysis result] Map: variable -> pc set
 *
 * Is used to represent the eg. the set of instructions
 * defining a certain variable *)
module VariableMap = struct
  include Map.Make(Variable)
  module KeySet = Set.Make(Variable)

  (* merge is defined as the union of their equally named sets *)
  let union =
    let merge_one _ a b : InstrSet.t option =
      match a, b with
      | None, None -> None
      | Some a, None -> Some a
      | None, Some b -> Some b
      | Some a, Some b -> Some (InstrSet.union a b) in
    merge merge_one

  let singleton var loc =
      add var (InstrSet.singleton loc) empty

  let equal =
    let is_equal a b = InstrSet.equal a b in
    equal is_equal

  let at var this =
    match find var this with
    | v -> v
    | exception Not_found -> InstrSet.empty
end

exception DeadCode of pc

(* returns a 'pc -> pc set' computing reaching definitions *)
let reaching (seg : segment) : pc -> InstrSet.t =
  let instrs = fst seg in
  let merge cur_defs in_defs =
    let merged = VariableMap.union cur_defs in_defs in
    if VariableMap.equal cur_defs merged then None else Some merged
  in
  let update pc defs =
    let instr = instrs.(pc) in
    (* add or override defined vars in one go*)
    let kill = VarSet.elements (TypedVarSet.untyped (defined_vars instr)) in
    let loc = InstrSet.singleton pc in
    let replace acc var = VariableMap.add var loc acc in
    List.fold_left replace defs kill
  in
  let res = forward_analysis VariableMap.empty seg merge update in
  fun pc ->
    let instr = instrs.(pc) in
    match res.(pc) with
    | None -> raise (DeadCode pc)
    | Some res ->
        let used = VarSet.elements (used_vars instr) in
        let definitions_of var = VariableMap.find var res in
        let all_definitions = List.map definitions_of used in
        List.fold_left InstrSet.union InstrSet.empty all_definitions


let liveness_analysis (seg : segment) =
  let instrs = fst seg in
  let merge cur_uses in_uses =
    let merged = VariableMap.union cur_uses in_uses in
    if VariableMap.equal cur_uses merged then None else Some merged
  in
  let update pc uses =
    let instr = instrs.(pc) in
    (* First remove defined vars *)
    let kill = VarSet.elements (TypedVarSet.untyped (defined_vars instr)) in
    let remove acc var = VariableMap.remove var acc in
    let uses = List.fold_left remove uses kill in
    (* Then add used vars *)
    let used = VarSet.elements (used_vars instr) in
    let merge acc var = VariableMap.union (VariableMap.singleton var pc) acc
    in
    List.fold_left merge uses used
  in
  backwards_analysis VariableMap.empty seg merge update


(* returns a 'pc -> variable set' computing live vars at a certain pc *)
let live (seg : segment) : pc -> variable list =
  let res = liveness_analysis seg in
  fun pc ->
    match res.(pc) with
    | None -> raise (DeadCode pc)
    | Some res ->
      let collect_key (key, value) = key in
      let live_vars = List.map collect_key (VariableMap.bindings res) in
      live_vars

(* returns a 'pc -> pc set' computing uses of a definition *)
let used (seg : segment) : pc -> InstrSet.t =
  let res = liveness_analysis seg in
  let instrs = fst seg in
  fun pc ->
    let instr = instrs.(pc) in
    match res.(pc) with
    | None -> raise (DeadCode pc)
    | Some res ->
        let defined = VarSet.elements (TypedVarSet.untyped (defined_vars instr)) in
        let uses_of var = VariableMap.at var res in
        let all_uses = List.map uses_of defined in
        List.fold_left InstrSet.union InstrSet.empty all_uses

