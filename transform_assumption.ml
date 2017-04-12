open Instr
open Transform_utils

(* Inserts checkpoints at all program points
 * A checkpoint is a well-formed osr point and a matching label.
 * For example:
 *   checkpoint_1:
 *     osr [] (func, version, checkpoint_1) [mut x = &x]
 * Initially the checkpoint is self referential (ie. its target is
 * the label right above. Insert assumption makes use of this property
 * to create a new version where the checkpoints are in sync.
 * This has to run before any optimistic optimizations. *)
let insert_checkpoints (func:afunction) =
  (* Can only insert checkpoints into an unoptimized function *)
  if List.length func.body <> 1 then None else

  let version = List.hd func.body in
  let instrs = version.instrs in
  let inp = Analysis.as_analysis_input func version in
  let scope = Scope.infer inp in
  let live = Analysis.live inp in

  let transform pc =
    let create_checkpoint pc =
      match scope.(pc) with
      | DeadScope -> assert(false)
      | Scope scope ->
        let osr = List.map (function
          | (Const_var, x) -> Osr_const (x, (Simple (Var x)))
          | (Mut_var, x)   ->
            if List.mem x (live (pc-1)) then
              Osr_mut_ref (x, x)
            else
              Osr_mut_undef x) (ModedVarSet.elements scope) in
        let target = { func=func.name; version=version.label; label=checkpoint_label pc } in
        Insert [Label (checkpoint_label pc); Osr {cond=[]; target; map=osr};]
    in
    if pc = 0 then Unchanged else
    match[@warning "-4"] instrs.(pc) with
    | Stop _ | Return _ | Label _ | Comment _ -> Unchanged
    | Osr _ -> assert false
    | _ -> create_checkpoint pc
  in
  let baseline = change_instrs transform inp in
  let (|?) opt def = match opt with Some v -> v | None -> def in
  Some { func with
         body = [
           { label = version.label;
             instrs = (|?) baseline instrs;
             annotations = None } ] }

let remove_empty_osr ({instrs} as inp) : instructions option =
  let transform pc =
    match[@warning "-4"] instrs.(pc) with
    | Osr {cond} when cond = [] -> Remove 1
    | _ -> Unchanged
  in
  change_instrs transform inp

(* TODO: replace this by a pass which does a global program transformation
 * and checks if the labels are really unused. *)
(* Removes all checkpoint labels. Can be applied as a final cleanup
 * when there are no osr-in points. *)
let remove_checkpoint_labels ({instrs} as inp) : instructions option =
  let transform pc =
    match[@warning "-4"] instrs.(pc) with
    | Label l when is_checkpoint_label l -> Remove 1
    | _ -> Unchanged
  in
  change_instrs transform inp

(* Inserts the assumption that osr_condition is false at position pc.
 * The approach is to
 * 1. Create a new version. This is a copy of the current one where all
 *    the osr targets point one version down (ie. to the current one).
 * 2. Starting from pc walk up the cfg and find the earliest possible
 *    checkpoint for the osr_condition. Branch targets are blocking as
 *    are instructions which interfere with the osr_condition. The
 *    condition has to be added to an existing osr instruction (see
 *    insert_checkpoints above). *)
let insert_assumption (func : afunction) osr_cond pc : version option =
  (* This takes the active version and duplicates it. Osr targets are
   * updated to point to the currently active version *)
  let next_version (func:afunction) =
    let cur_version = Instr.active_version func in
    let transform pc =
      match[@warning "-4"] cur_version.instrs.(pc) with
      | Osr {cond; target={func; version; label}; map} ->
        let target = {func; version = cur_version.label; label} in
        Replace (Osr {cond; target; map})
      | _ -> Unchanged
    in
    let inp = Analysis.as_analysis_input func cur_version in
    { label = Edit.fresh_version_label func cur_version.label;
      instrs = (match change_instrs transform inp with | None -> cur_version.instrs | Some i -> i);
      annotations = None }
  in

  let version = next_version func in
  let instrs = version.instrs in
  let preds = Analysis.predecessors version.instrs in
  (* Finds the highest up osr checkpoint in that basic block where the
   * assumption can be placed. *)
  let rec find_candidate_osr cond_vars pc acc =
    if pc = 0 then acc else
    match[@warning "-4"] instrs.(pc) with
    | Osr _ -> find_candidate_osr cond_vars (pc-1) (Some pc)
    | Label _ ->
      begin match[@warning "-4"] preds.(pc) with
      | [pred] -> find_candidate_osr cond_vars pred acc
      | _ -> acc
      end
    | _ ->
      assert (preds.(pc) = [pc-1]);
      if Instr.independent instrs.(pc) osr_cond
      then find_candidate_osr cond_vars (pc-1) acc
      else acc
  in
  let osr_vars = expr_vars osr_cond in
  begin match find_candidate_osr osr_vars (pc-1) None with
  | None -> None
  | Some pc ->
    begin match[@warning "-4"] instrs.(pc) with
    | Osr {cond; target; map} ->
      instrs.(pc) <- Osr {cond=osr_cond::cond; target; map};
      Some { version with instrs }
    | _ -> assert (false)
    end
  end
