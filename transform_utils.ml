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
        (* Insert at the instruction stream position before the label. This is does not correspond
         * to before in the sense of control flow. *)
        assert(is_label pc);
        acc_instr (pc+1) (instrs.(pc) :: List.rev_append is acc) true
      | InsertAfter is ->
        acc_instr (pc+1) (List.rev_append is (instrs.(pc) :: acc)) true
      | Unchanged ->
        acc_instr (pc+1) (instrs.(pc)::acc) changed
  in
  acc_instr 0 [] false

(* This util can fix the scope after inserting a fresh variable in the graph.
 * As an additional sideeffect it will make every drop explicit. *)
let fix_scope : transform_instructions = fun {formals; instrs} ->
  let merge pc cur incom =
    let res = VarSet.inter cur incom in
    if VarSet.equal res cur then None else Some res
  in
  let update pc cur =
    let instr = instrs.(pc) in
    let added = Instr.declared_vars instr in
    let updated = VarSet.union cur added in
    let dropped = Instr.dropped_vars instr in
    VarSet.diff updated dropped
  in
  let initial_state = VarSet.of_list formals in
  let scope = Analysis.forward_analysis initial_state instrs merge update in
  let succs = Analysis.successors instrs in
  let transform pc =
    (* Thanks to the normalized graph structure only before gotos the scope has to be aligned *)
    match[@warning "-4"] instrs.(pc) with
    | Goto _ ->
      let succs = succs.(pc) in
      assert(List.length succs <= 2);
      let my_scope = scope pc in
      let succ_scopes = List.map (fun pc -> scope pc) succs in
      let min_scope = List.fold_left VarSet.union VarSet.empty succ_scopes in
      (* Because of split edge all the succs should agree on one scope *)
      assert (succs = [] || VarSet.equal (List.hd succ_scopes) min_scope);

      let to_drop = VarSet.diff my_scope min_scope in
      let to_drop = VarSet.diff to_drop (dropped_vars instrs.(pc)) in
      let to_drop_instrs = List.map (fun var -> Drop var) (VarSet.elements to_drop) in
      InsertBefore to_drop_instrs
    | _ ->
      Unchanged
  in
  change_instrs transform {formals;instrs}
