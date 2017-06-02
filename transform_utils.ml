open Instr
open Types

type instruction_change =
  | Remove of int
  | InsertAfter of instruction list
  | InsertBefore of instruction list
  | Replace of instruction list
  | InsertBeforeLabel of instruction list
  | ReplaceLabel of instruction list
  | Unchanged

let change_instrs (transform : pc -> instruction_change) ({formals; instrs} : analysis_input) =
  let rec acc_instr pc acc changed =
    if pc = Array.length instrs then
      if changed then Some (Array.of_list (List.rev acc)) else None
    else
      let is_label pc = match[@warning "-4"] instrs.(pc) with | Label _ -> true | _ -> false in
      match transform pc with
      | Remove n ->
        acc_instr (pc+n) acc true
      | Replace is ->
        (* Replacing a label is dangerous... Better be sure *)
        assert(not (is_label pc));
        acc_instr (pc+1) (List.rev_append is acc) true
      | InsertBefore is ->
        (* Inserting before a label is undefined. There is no sensible definition of what
         * position is 'before'. *)
        assert(not (is_label pc));
        acc_instr (pc+1) (instrs.(pc) :: List.rev_append is acc) true
      | ReplaceLabel is ->
        assert(is_label pc);
        acc_instr (pc+1) (List.rev_append is acc) true
      | InsertBeforeLabel is ->
        assert(is_label pc);
        acc_instr (pc+1) (instrs.(pc) :: List.rev_append is acc) true
      | InsertAfter is ->
        acc_instr (pc+1) (List.rev_append is (instrs.(pc) :: acc)) true
      | Unchanged ->
        acc_instr (pc+1) (instrs.(pc)::acc) changed
  in
  acc_instr 0 [] false
