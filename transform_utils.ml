open Instr

type instruction_change =
  | Remove of int
  | Insert of instruction list
  | InsertAfter of instruction list
  | Replace of instruction
  | Unchanged

let change_instrs (transform : pc -> instruction_change) ({formals; instrs} : analysis_input) =
  let rec acc_instr pc acc changed =
    if pc = Array.length instrs then
      if changed then Some (Array.of_list (List.rev acc)) else None
    else
      match transform pc with
      | Remove n ->
        acc_instr (pc+n) acc true
      | Replace i ->
        acc_instr (pc+1) (i :: acc) true
      | Insert is ->
        acc_instr (pc+1) (instrs.(pc) :: (List.rev is) @ acc) true
      | InsertAfter is ->
        acc_instr (pc+1) ((List.rev is) @ instrs.(pc) :: acc) true
      | Unchanged ->
        acc_instr (pc+1) (instrs.(pc)::acc) changed
  in
  acc_instr 0 [] false
