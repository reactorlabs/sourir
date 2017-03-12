open Instr

(* TODO remove the fallthrough cases *)

let split_edge instrs pc label pc' =
  assert (instrs.(pc') = Label label);
  let split_label = Rename.fresh_label instrs label in
  let split_edge = [|
    Label split_label;
    Goto label;
  |] in
  (* insert the split edge *)
  let new_instrs = Edit.subst instrs pc' 0 split_edge in
  (* then rewrite the branch instruction *)
  let new_pc = Edit.subst_pc instrs pc' 0 split_edge in
  let new_branch = match[@warning "-4"] instrs.(pc) with
    | Branch (v, l1, l2) ->
      if l1 = label
      then Branch (v, split_label, l2)
      else if l2 = label
      then Branch (v, l1, split_label)
      else invalid_arg "split_edge"
    | _ -> invalid_arg "split_edge" in
  new_instrs.(new_pc pc) <- new_branch;
  new_instrs, new_pc

type push_status = Blocked | Need_pull of pc | Stop | Work of pc list

let push_drop instrs dropped_var pc_drop =
  let pc_above = pc_drop - 1 in
  assert (instrs.(pc_drop) = Drop dropped_var);
  let instr = instrs.(pc_above) in
  let _succs = Analysis.successors instrs in
  let preds = Analysis.predecessors instrs in
  let blocking_instr instr =
    VarSet.mem dropped_var (required_vars instr) in
  let edit new_instrs =
    Edit.subst instrs pc_above 2 new_instrs in
  let general_regime instr =
    if blocking_instr instr then instrs, Blocked
    else edit [|Drop dropped_var; instr|], Work [pc_above] in
  match instr with
  | Assign (x, _) | Clear x ->
    (* if the current instruction defined the dropped variable,
       we can delete the instruction *)
    if x = dropped_var
    then edit [|Drop dropped_var|], Work [pc_above]
    else general_regime instr
  | Decl_const (x, _) | Decl_mut (x, _) ->
    (* if the current instruction declared the dropped variable, we
       can delete the instruction, and we must also forget about the
       drop *)
    if x = dropped_var
    then edit [||], Stop
    else general_regime instr
  | Stop ->
    (* we are coming from the predecessors, cannot reach a Stop! *)
    assert false
  | (Read _ | Branch _ | Osr _ | Drop _ | Goto _ | Comment _ | Print _) as instr ->
    general_regime instr
  | Label label
    when List.exists (fun pc -> blocking_instr instrs.(pc)) preds.(pc_above)
    -> instrs, Blocked
  | Label label ->
    (*
       We don't want to push over branches; they are barriers
       that will pull in another phase.

       But, if we have several predecessors, some of which are
       branches, we need to split those branch edges to push
       independently to all predecessor edges.
    *)
    let is_branch pred_pc = match[@warning "-4"] instrs.(pred_pc) with
      | Branch _ -> true
      | _ -> false in
    begin match List.find is_branch preds.(pc_above) with
    | branch_pc ->
     if preds.(pc_above) = [branch_pc] then instrs, Need_pull branch_pc
     else
       (* multi-predecessor case, one of which is a branch:
          we just split the branch edge -- doing anything more
          would be fragile as we changed the instructions.

          Iterating this transform will eventually remove all
          branch edges from our (multi)predecessors, so that the
          Not_found case below will do the final push. *)
       let instrs, pc_map = split_edge instrs branch_pc label pc_above in
       instrs, Work [pc_map pc_drop]
   | exception Not_found ->
     let delete = (pc_drop, 1, [||]) in
     let insert pred_pc = (pred_pc, 0, [| Drop dropped_var |]) in
     let substs = delete :: List.map insert preds.(pc_above) in
     let instrs, pc_map = Edit.subst_many instrs substs in
     let list = List.map (fun pc -> pc_map pc - 1) preds.(pc_above) in
     instrs, Work (List.sort Pervasives.compare list)
   end

type pull_status = Pulled_to of pc | Blocked

let pull_drop instrs dropped_var pc_branch =
  let drop_instr = Drop dropped_var in
  let succs = Analysis.successors instrs in
  let instr_after pc = instr_at instrs (pc+1) in
  let to_pull = List.map instr_after succs.(pc_branch) in
  let can_pull = List.for_all ((=) drop_instr) to_pull in
  if not can_pull then instrs, Blocked
  else begin
    let insert = (pc_branch, 0, [| drop_instr |]) in
    let delete label_pc = (label_pc + 1, 1, [||]) in
    let deletes = List.map delete succs.(pc_branch) in
    let instrs, pc_map = Edit.subst_many instrs (insert :: deletes) in
    instrs, Pulled_to (pc_map pc_branch - 1)
  end

