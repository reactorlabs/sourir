open Instr
open Types

type push_status =
  | Stop of Edit.result
  | Blocked
  | Need_pull of pc
  | Work of Edit.result * pc list

type conditions = {
  is_eliminating : instruction -> bool;
  is_annihilating : instruction -> bool;
  is_blocking : instruction -> bool;
}

let push_instr cond instrs pc : push_status =
  let { is_eliminating; is_annihilating; is_blocking } = cond in
  assert (pc > 0);
  let pc_above = pc - 1 in
  let to_move = instrs.(pc) in
  let instr = instrs.(pc_above) in
  let preds = Analysis.predecessors instrs in
  let edit new_instrs =
    Edit.subst instrs pc_above 2 new_instrs in
  match[@warning "-4"] instr with
  | Stop _ | Return _ ->
    (* we are coming from the predecessors, cannot reach a Stop! *)
    assert false
  | Label (BranchLabel label) ->
    (*
       We don't want to push over branches; they are barriers
       that will pull in another phase.
    *)
    begin match preds.(pc_above) with
    | [branch_pc] ->
      if is_blocking instrs.(branch_pc) then Blocked else Need_pull branch_pc
    | _ -> assert (false) (* not possible on a well-formed graph *)
    end
  | Label (MergeLabel label) ->
     let move_and_work pred_pc =
       match[@warning "-4"] instrs.(pred_pc) with
       | Goto label_ ->
         assert (label = label_);
         (pred_pc, 0, [| to_move |]), (fun pc_map -> pc_map pred_pc - 1)
       | _ -> assert (false) (* not possible on a well-formed graph *)
     in
     let moves, next = List.split (List.map move_and_work preds.(pc_above)) in
     let delete = (pc, 1, [||]) in
     let (_instrs, pc_map) as edit = Edit.subst_many instrs (delete :: moves) in
     let worklist =
       next
       |> List.map (fun next -> next pc_map)
       |> List.sort Pervasives.compare in
     Work (edit, worklist)
  | _ as instr ->
    if is_eliminating instr then Work (edit [|to_move|], [pc_above])
    else if is_annihilating instr then Stop (edit [||])
    else if is_blocking instr then Blocked
    else Work (edit [|to_move; instr|], [pc_above])

type pull_status =
  | Pulled_to of Edit.result * pc
  | Blocked

let try_pull instrs pc_branch : pull_status =
  let succs = Analysis.successors instrs in
  if pc_branch = Array.length instrs then Blocked else
  let instr_after_label pc =
    assert (match[@warning "-4"] instrs.(pc) with
        | Label _ -> true | _ -> false);
    instrs.(pc+1) in
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

let pull_instr cond instrs pc =
  let rec work_push instrs progress to_push to_pull =
    match to_push with
    | pc :: to_push ->
      if pc = 0 then work_push instrs progress to_push to_pull
      else begin match push_instr cond instrs pc with
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
      begin match try_pull instrs pc with
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

let pull is_target cond instrs =
    (* Loop around and move all drops until none moves anymore *)
    let rec work status instrs pc =
      let at_end = Array.length instrs = pc in
      if at_end then
        match status with
        | Stuck -> None
        | Made_progress ->
          begin match work Stuck instrs 0 with
            | None -> Some instrs
            | Some instrs -> Some instrs
          end
      else if is_target instrs.(pc) then
        begin match pull_instr cond instrs [pc] with
          | None -> work status instrs (pc+1)
          | Some instrs -> work Made_progress instrs 0
        end
      else
        work status instrs (pc+1)
    in
    work Stuck instrs 0


module Drop = struct
  (* TODO:
   * If we ever add mutable return values or duplicating refs this breaks!
   *
   * Example (the drop will be moved over the print):
   *
   * function foo (mut x)
   *   return &x
   *
   * function main ()
   *   mut x = 1
   *   mut y = foo(&x)
   *   print (y)
   *   drop x
   *
   *)
  let is_blocking var instr =
    match[@warning "-4"] instr with
    | Call (x, _, _) when x = var -> true
    | _ -> VarSet.mem var (required_vars instr)

  let is_eliminating var instr =
    match[@warning "-4"] instr with
    | Assign (x, _) -> x = var
    | _ -> false

  let is_annihilating var instr =
    match[@warning "-4"] instr with
    | Decl_var (x, _) -> x = var
    | _ -> false

  let conditions_var var = {
    is_blocking = is_blocking var;
    is_eliminating = is_eliminating var;
    is_annihilating = is_annihilating var;
  }

  let pull_var instrs var =
    let is_target instr =
      match[@warning "-4"] instr with
      | Drop x when x = var -> true
      | _ -> false
    in
    pull is_target (conditions_var var) instrs

  let apply : transform_instructions = fun {formals; instrs} ->
    let collect vars instr =
      match[@warning "-4"] instr with
      | Drop x -> VarSet.add x vars
      | _ -> vars
    in
    let dropped_vars = Array.fold_left collect VarSet.empty instrs in
    let rec work instrs vars changed =
      match vars with
      | var :: rest ->
        begin match pull_var instrs var with
        | None -> work instrs rest changed
        | Some instrs -> work instrs (var :: rest) true
        end
      | [] -> instrs, changed
    in
    let res, changed = work instrs (VarSet.elements dropped_vars) false in
    if changed then Some res else None
end
