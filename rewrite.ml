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

let push_instr is_eliminating is_anihilating is_blocking instrs pc : push_status =
  assert (pc >0);
  let pc_above = pc - 1 in
  let to_move = instrs.(pc) in
  let instr = instrs.(pc_above) in
  let preds = Analysis.predecessors instrs in
  let edit new_instrs =
    Edit.subst instrs pc_above 2 new_instrs in
  match[@warning "-4"] instr with
  | Stop ->
    (* we are coming from the predecessors, cannot reach a Stop! *)
    assert false
  | Label label
    when List.exists (fun pc -> is_blocking instrs.(pc)) preds.(pc_above)
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
       Work (edit, [pc_map pc])
   | exception Not_found ->
     (* multi-predecessor case, with no multi-successor predecessor (no branch);
        we can move the drop above all predecessors. For a predecessor in (pc),
        we move the drop to ((pc_map pc) - 1), that is above a (Goto label)
        instruction at (pc_map pc). This assumes that there is no fallthrough
        to our label, that [Transform.remove_fallthroughs_to_label] has been
        applied to the input program. *)
     let delete = (pc, 1, [||]) in
     let insert pred_pc = (pred_pc, 0, [| to_move |]) in
     let substs = delete :: List.map insert preds.(pc_above) in
     let (_instrs, pc_map) as edit = Edit.subst_many instrs substs in
     let list = List.map (fun pc -> pc_map pc - 1) preds.(pc_above) in
     Work (edit, List.sort Pervasives.compare list)
   end
  | _ as instr ->
    if is_eliminating instr then Work (edit [|to_move|], [pc_above])
    else if is_anihilating instr then Stop (edit [||])
    else if is_blocking instr then Blocked
    else Work (edit [|to_move; instr|], [pc_above])

type pull_status =
  | Pulled_to of Edit.result * pc
  | Blocked

let pull_instr instrs pc_branch : pull_status =
  let succs = Analysis.successors instrs in
  let instr_after_label pc =
    assert (match[@warning "-4"] instrs.(pc) with
        | Label _ -> true | _ -> false);
    instr_at instrs (pc+1) in
  let to_pull = List.map instr_after_label succs.(pc_branch) in
  let sample_instr = List.hd to_pull in
  let can_pull = List.for_all ((=) sample_instr) to_pull in
  if not can_pull then Blocked
  else begin
    let insert = (pc_branch, 0, [| sample_instr |]) in
    let delete label_pc = (label_pc + 1, 1, [||]) in
    let deletes = List.map delete succs.(pc_branch) in
    let (_instrs, pc_map) as edit = Edit.subst_many instrs (insert :: deletes) in
    Pulled_to (edit, pc_map pc_branch - 1)
  end

type progress = Made_progress | Stuck

let move_up_instr is_eliminating is_anihilating is_blocking instrs pc =
  let push_instr = push_instr is_eliminating is_anihilating is_blocking in
  let rec work_push instrs progress to_push to_pull =
    match to_push with
    | pc :: to_push ->
      begin match push_instr instrs pc with
        | Blocked ->
          work_push instrs progress to_push to_pull
        | Stop (instrs, pc_map) ->
          let (!!) = List.map pc_map in
          work_push instrs progress !!to_push !!to_pull
        | Need_pull pc' ->
          work_push instrs progress to_push (pc' :: to_pull)
        | Work ((instrs, pc_map), pcs) ->
          let (!!) = List.map pc_map in
          work_push instrs Made_progress (List.rev_append pcs !!to_push) !!to_pull
      end
    | [] -> work_pull instrs progress to_pull []
  and work_pull instrs progress to_pull blocked_branches =
    match to_pull with
    | pc :: to_pull ->
      begin match pull_instr instrs pc with
        | Pulled_to ((instrs, pc_map), pc') ->
          let (!!) = List.map pc_map in
          work_push instrs Made_progress [pc'] (List.rev_append !!blocked_branches !!to_pull)
        | Blocked ->
          work_pull instrs progress to_pull (pc :: blocked_branches)
      end
    | [] ->
      match progress with
      | Stuck ->
        None
      | Made_progress ->
        Some instrs
  in
  work_push instrs Stuck pc []

let move_up is_target is_eliminating is_anihilating is_blocking instrs =
    let move_up_instr = move_up_instr is_eliminating is_anihilating is_blocking in

    (* Loop around and move all drops until none moves anymore *)
    let rec work status instrs pc =
      let at_end = Array.length instrs = pc in
      if at_end then
        match status with
        | Stuck -> None
        | Made_progress ->
          let instrs = match work Stuck instrs 0 with
            | Some instrs -> instrs
            | None -> instrs
          in
          Some instrs
      else if is_target instrs.(pc) then
        begin match move_up_instr instrs [pc] with
          | None -> work status instrs (pc+1)
          | Some instrs -> work Made_progress instrs 0
        end
      else
        work status instrs (pc+1)
    in
    work Stuck instrs 0


module Drop = struct
  let is_blocking var instr =
    VarSet.mem var (required_vars instr)

  let is_eliminating var instr =
    match[@warning "-4"] instr with
    | Assign (x, _) | Clear x -> x = var
    | _ -> false

  let is_anihilating var instr =
    match[@warning "-4"] instr with
    | Decl_const (x, _) | Decl_mut (x, _) -> x = var
    | _ -> false

  let move_up_var instrs var =
    let is_target instr =
      match[@warning "-4"] instr with
      | Drop x when x = var -> true
      | _ -> false
    in
    let move = move_up
        is_target
        (is_eliminating var) (is_anihilating var) (is_blocking var) in
    move instrs

  let move_up instrs =
    let collect vars instr =
      match[@warning "-4"] instr with
      | Drop x -> VarSet.add x vars
      | _ -> vars
    in
    let dropped_vars = Array.fold_left collect VarSet.empty instrs in
    let rec work instrs vars =
      match vars with
      | var :: rest ->
        begin match move_up_var instrs var with
        | None -> work instrs rest
        | Some instrs -> work instrs (var :: rest)
        end
      | [] -> instrs
    in
    work instrs (VarSet.elements dropped_vars)
end
