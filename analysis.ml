open Instr

let successors program pc =
  let pc' = pc + 1 in
  let next = if pc' = Array.length program then [] else [pc'] in
  let resolve = Instr.resolve program in
  match program.(pc) with
  | Decl_const _
  | Decl_mut _
  | Assign _
  | Label _
  | Comment _
  | Read _
  | Print _ -> next
  | Goto l -> [resolve l]
  | Invalidate (_, l, _) -> next @ [resolve l]
  | Branch (_e, l1, l2) -> [resolve l1; resolve l2]
  | Stop -> []

let predecessors program =
  let preds = Array.map (fun _ -> []) program in
  let mark_successor pc pc' =
    preds.(pc') <- pc :: preds.(pc') in
  for pc = 0 to Array.length program - 1 do
    List.iter (mark_successor pc) (successors program pc)
  done;
  preds

(* Perform forward analysis on some code
 *
 * init_state : list of (Initial input state, first instruction)
 * merge      : current state -> input state -> merge state if changed
 * update     : instruction -> input state -> output state
 * program    : array of instructions
 *
 * Returns an array of states for every instruction of the program.
 * Bottom is represented as None *)

let forward_analysis (init_state : ('a * pc))
                     (merge : 'a -> 'a -> 'a option)
                     (update : pc -> 'a -> 'a)
                     (program : program)
                     : 'a option array =
  let program_state = Array.map (fun _ -> ref None) program in
  let rec work = function
    | [] -> ()
    | (in_state, pc) :: rest ->
        let cell = program_state.(pc) in
        let merged =
          match !cell with
          | None -> Some in_state
          | Some cur_state -> merge cur_state in_state
        in begin match merged with
        | None -> work rest
        | Some merged ->
            cell := Some merged;
            let updated = update pc merged in
            let succs = successors program pc in
            let new_work = List.map (fun pc -> (updated, pc)) succs in
            work (new_work @ rest)
        end
  in
  work [init_state];
  Array.map (!) program_state

let exits program =
  let rec exits pc : Pc.t list =
    if Array.length program = pc then []
    else
      ((if List.length (successors program pc) = 0 then [pc] else [])
        @ exits (pc + 1)) in
  exits 0

let do_backwards_analysis (init_state : ('a * pc) list)
                          (merge : 'a -> 'a -> 'a option)
                          (update : pc -> 'a -> 'a)
                          (program : program)
                          : 'a option array =
  let program_state = Array.map (fun _ -> ref None) program in
  let predecessors = predecessors program in
  let rec work = function
    | [] -> ()
    | (in_state, pc) :: rest ->
        let cell = program_state.(pc) in
        let merged =
          match !cell with
          | None -> Some in_state
          | Some cur_state -> merge cur_state in_state
        in begin match merged with
        | None -> work rest
        | Some merged ->
            cell := Some merged;
            let updated = update pc merged in
            let pred = predecessors.(pc) in
            let new_work = List.map (fun pc -> (updated, pc)) pred in
            work (new_work @ rest)
        end
  in
  work init_state;
  Array.map (!) program_state


module InstrSet = Set.Make(Pc)
module Def = struct
  type t = variable
  let compare = Variable.compare
end
module Defs = Map.Make(Def)

let backwards_analysis (merge : 'a -> 'a -> 'a option)
                       (update : pc -> 'a -> 'a)
                       (program : program)
                       : 'a option array =
  let exits = exits program in
  let init_state = List.map (fun pc -> (Defs.empty, pc)) exits in
  do_backwards_analysis init_state merge update program

let merge_defs =
  let do_merge _ a b : InstrSet.t option =
    match a, b with
    | None, None -> None
    | Some a, None -> Some a
    | None, Some b -> Some b
    | Some a, Some b -> Some (InstrSet.union a b) in
  Defs.merge do_merge

let equal_defs =
  let do_equal a b = InstrSet.equal a b in
  Defs.equal do_equal


let reaching prog pc =
  let instr = prog.(pc) in
  let init_state = (Defs.empty, 0) in
  let merge cur_def in_def =
    let merged = merge_defs cur_def in_def in
    if equal_defs cur_def merged then None else Some merged in
  let update pc defs =
    let instr = prog.(pc) in
    match defined_vars instr with
    | None -> defs
    | Some x -> Defs.add x (InstrSet.singleton pc) defs in
  let res = forward_analysis init_state merge update prog in
  match res.(pc) with
  | None -> InstrSet.empty
  | Some res ->
      let rec union a =
        match a with
        | [] -> InstrSet.empty
        | a :: tail -> InstrSet.union a (union tail)
      in
      let consumed_vars = consumed_vars instr in
      let definitions_of var = Defs.find var res in
      let all_definitions = List.map definitions_of consumed_vars in
      union all_definitions

let used prog pc =
  let instr = prog.(pc) in
  let merge cur_def in_def =
    let merged = merge_defs cur_def in_def in
    if equal_defs cur_def merged then None else Some merged in
  let update pc defs =
    let instr = prog.(pc) in
    let defined =
      match defined_vars instr with
      | None -> defs
      | Some var -> Defs.remove var defs in
    let merge acc var =
      let insert = Defs.add var (InstrSet.singleton pc) Defs.empty in
      merge_defs insert acc in
    List.fold_left merge defined (consumed_vars instr) in
  let res = backwards_analysis merge update prog in
  match res.(pc) with
  | None -> InstrSet.empty
  | Some res ->
      let defined_vars = defined_vars instr in
      match defined_vars with
      | None -> InstrSet.empty
      | Some var ->
          let uses_of var = Defs.find var res in
          match uses_of var with
          | e -> e
          | exception Not_found -> InstrSet.empty
