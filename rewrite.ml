open Instr

(** [split_edge instrs pc label pc']
    splits the edge from a branch instruction in [pc]
    to a [Label label] instruction in [pc'],
    assuming there is no fallthrough to [pc'] -- all
    other predecessors are gotos or branches.

    Before applying it to arbitrary program, we use
    [Transform.remove_fallthroughs_to_label] to make the
    assumption hold.
*)
let split_edge instrs pc label pc' =
  assert (instrs.(pc') = Label label);
  let split_label = Rename.fresh_label instrs label in
  let split_edge = [|
    Label split_label;
    Goto label;
  |] in
  (* insert the split edge *)
  let new_instrs, pc_map = Edit.subst instrs pc' 0 split_edge in
  let new_branch = match[@warning "-4"] instrs.(pc) with
    | Branch (v, l1, l2) ->
      if l1 = label
      then Branch (v, split_label, l2)
      else if l2 = label
      then Branch (v, l1, split_label)
      else invalid_arg "split_edge"
    | _ -> invalid_arg "split_edge" in
  new_instrs.(pc_map pc) <- new_branch;
  new_instrs, pc_map

type push_status =
  | Stop of Edit.result
  | Blocked
  | Need_pull of pc
  | Work of Edit.result * pc list

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
    if blocking_instr instr then Blocked
    else Work (edit [|Drop dropped_var; instr|], [pc_above]) in
  match instr with
  | Assign (x, _) | Clear x ->
    (* if the current instruction defined the dropped variable,
       we can delete the instruction *)
    if x = dropped_var
    then Work (edit [|Drop dropped_var|], [pc_above])
    else general_regime instr
  | Decl_const (x, _) | Decl_mut (x, _) ->
    (* if the current instruction declared the dropped variable, we
       can delete the instruction, and we must also forget about the
       drop *)
    if x = dropped_var
    then Stop (edit [||])
    else general_regime instr
  | Stop ->
    (* we are coming from the predecessors, cannot reach a Stop! *)
    assert false
  | (Read _ | Branch _ | Osr _ | Drop _ | Goto _ | Comment _ | Print _) as instr ->
    general_regime instr
  | Label label
    when List.exists (fun pc -> blocking_instr instrs.(pc)) preds.(pc_above)
    -> Blocked
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
     if preds.(pc_above) = [branch_pc] then Need_pull branch_pc
     else
       (* multi-predecessor case, one of which is a branch:
          we just split the branch edge -- doing anything more
          would be fragile as we changed the instructions.

          Iterating this transform will eventually remove all
          branch edges from our (multi)predecessors, so that the
          Not_found case below will do the final push. *)
       let (_instrs, pc_map) as edit = split_edge instrs branch_pc label pc_above in
       Work (edit, [pc_map pc_drop])
   | exception Not_found ->
     (* multi-predecessor case, with no multi-successor predecessor (no branch);
        we can move the drop above all predecessors. For a predecessor in (pc),
        we move the drop to ((pc_map pc) - 1), that is above a (Goto label)
        instruction at (pc_map pc). This assumes that there is no fallthrough
        to our label, that [Transform.remove_fallthroughs_to_label] has been
        applied to the input program. *)
     let delete = (pc_drop, 1, [||]) in
     let insert pred_pc = (pred_pc, 0, [| Drop dropped_var |]) in
     let substs = delete :: List.map insert preds.(pc_above) in
     let (_instrs, pc_map) as edit = Edit.subst_many instrs substs in
     let list = List.map (fun pc -> pc_map pc - 1) preds.(pc_above) in
     Work (edit, List.sort Pervasives.compare list)
   end

type pull_status =
  | Pulled_to of Edit.result * pc
  | Blocked

let pull_drop instrs dropped_var pc_branch =
  let drop_instr = Drop dropped_var in
  let succs = Analysis.successors instrs in
  let instr_after pc = instr_at instrs (pc+1) in
  let to_pull = List.map instr_after succs.(pc_branch) in
  let can_pull = List.for_all ((=) drop_instr) to_pull in
  if not can_pull then Blocked
  else begin
    let insert = (pc_branch, 0, [| drop_instr |]) in
    let delete label_pc = (label_pc + 1, 1, [||]) in
    let deletes = List.map delete succs.(pc_branch) in
    let (_instrs, pc_map) as edit = Edit.subst_many instrs (insert :: deletes) in
    Pulled_to (edit, pc_map pc_branch - 1)
  end

type progress = Made_progress | Stuck

let debug =false

let move_drops_on_var instrs dropped_var =
  let is_drop_on_var pc = match[@warning "-4"] instrs.(pc) with
    | Drop x -> x = dropped_var
    | _ -> false in
  let drop_pcs =
    instrs
    |> Array.mapi (fun pc _instr -> pc)
    |> Array.to_list
    |> List.filter is_drop_on_var in
  let rec push instrs progress to_push to_pull =
    match to_push with
    | pc :: to_push ->
      begin match push_drop instrs dropped_var pc with
        | Blocked ->
          push instrs progress to_push to_pull
        | Stop (instrs, pc_map) ->
          let (!!) = List.map pc_map in
          push instrs progress !!to_push !!to_pull
        | Need_pull pc' ->
          push instrs progress to_push (pc' :: to_pull)
        | Work ((instrs, pc_map), pcs) ->
          let (!!) = List.map pc_map in
          push instrs Made_progress (List.rev_append pcs !!to_push) !!to_pull
      end
    | [] -> pull instrs progress to_pull []
  and pull instrs progress to_pull blocked_branches =
    match to_pull with
    | pc :: to_pull ->
      begin match pull_drop instrs dropped_var pc with
        | Pulled_to ((instrs, pc_map), pc') ->
          let (!!) = List.map pc_map in
          push instrs Made_progress [pc'] (List.rev_append !!blocked_branches !!to_pull)
        | Blocked ->
          pull instrs progress to_pull (pc :: blocked_branches)
      end
    | [] ->
      match progress with
      | Stuck ->
        None
      | Made_progress ->
        Some instrs
  in
  push instrs Stuck drop_pcs []

let move_drops instrs =
  let instrs = Transform.remove_fallthroughs_to_label instrs in
  let collect dropped_vars instr =
    match[@warning "-4"] instr with
    | Drop x -> VarSet.add x dropped_vars
    | _ -> dropped_vars in
  let dropped_vars = Array.fold_left collect VarSet.empty instrs in
  let rec work instrs blocked todo = match todo with
    | [] -> instrs
    | var :: todo ->
      begin match move_drops_on_var instrs var with
        | None -> work instrs (var :: blocked) todo
        | Some instrs -> work instrs [] (todo @ blocked @ [var])
      end
  in
  work instrs [] (VarSet.elements dropped_vars)
