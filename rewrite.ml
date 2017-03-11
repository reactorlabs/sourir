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

type status = Blocked | Need_pull | Stop | Work of pc list

let push_drop instrs pc_drop =
  let pc_above = pc_drop - 1 in
  let dropped_var = match[@warning "-4"] instrs.(pc_drop) with
    | Drop x -> x
    | _ -> invalid_arg "push_drop"
  in
  let instr = instrs.(pc_above) in
  let _succs = Analysis.successors instrs in
  let preds = Analysis.predecessors instrs in
  let edit new_instrs =
    Edit.subst instrs pc_above 2 new_instrs in
  let general_regime instr =
    if VarSet.mem dropped_var (required_vars instr)
    then instrs, Blocked
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
     if preds.(pc_above) = [branch_pc] then instrs, Need_pull
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
     let insert pred_pc = (pred_pc, 0, [|Drop dropped_var|]) in
     let substs = delete :: List.map insert preds.(pc_above) in
     let instrs, pc_map = Edit.subst_many instrs substs in
     let list = List.map (fun pc -> pc_map pc - 1) preds.(pc_above) in
     instrs, Work (List.sort Pervasives.compare list)
   end

