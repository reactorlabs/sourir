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

let local_predecessors program pc =
  let before =
    if pc == 0 then []
    else
      let pc' = pc - 1 in
      match program.(pc') with
      | Decl_const _
      | Decl_mut _
      | Assign _
      | Label _
      | Comment _
      | Read _
      | Invalidate _
      | Print _ -> [pc']
      | Goto _
      | Branch _
      | Stop -> []
  in
  let jmps =
    let find_origins label =
      let rec find_origins pc =
        if Array.length program = pc then []
        else
          let pc' = pc + 1 in
          match program.(pc) with
          | Goto l when l = label -> pc :: find_origins pc'
          | Branch (_, l1, l2) when l1 = label || l2 = label -> pc :: find_origins pc'
          | Invalidate (_, l, _) when l = label -> pc :: find_origins pc'
          | _ -> find_origins pc'
      in
      find_origins 0
    in
    match program.(pc) with
    | Label l -> find_origins l
    | _ -> []
  in
  before @ jmps

let test_global_predecessors preds program =
  let module PcSet = Set.Make(struct type t = int let compare : int -> _ = compare end) in
  for pc = 0 to Array.length program - 1 do
    assert (PcSet.equal
              (PcSet.of_list preds.(pc) )
              (PcSet.of_list (local_predecessors program pc)));
  done;
  ()

let global_predecessors program =
  let preds = Array.map (fun _ -> []) program in
  let mark_successor pc pc' =
    preds.(pc') <- pc :: preds.(pc') in
  for pc = 0 to Array.length program - 1 do
    List.iter (mark_successor pc) (successors program pc)
  done;
  test_global_predecessors preds program;
  preds

let predecessors program pc =
  (global_predecessors program).(pc)

module VarSet = Set.Make(Variable)

(* Perform forward analysis on some code
 *
 * init_state : Initial input state and first instruction
 * merge      : current state -> input state -> merge state if changed
 * update     : abstract instruction -> input state -> output state
 * program    : array of abstract instructions
 * prog_at    : program -> index -> instruction at index
 *
 * Returns an array of states for every instruction of the program.
 * Bottom is represented as None *)

let forward_analysis (init_state : ('a * int))
                     (merge : 'a -> 'a -> 'a option)
                     (update : int -> 'a -> 'a)
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
