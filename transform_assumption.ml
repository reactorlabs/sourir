open Instr
open Types
open Transform_utils

(* Inserts checkpoints at all program points
 * A checkpoint is a well-formed assumption point and a matching label.
 * For example:
 *   checkpoint_1:
 *     assume [] (func, version, checkpoint_1) [mut x = &x]
 * Initially the checkpoint is self referential (ie. its target is
 * the label right above. Insert assumption makes use of this property
 * to create a new version where the checkpoints are in sync.
 * This has to run before any optimistic optimizations. *)
let insert_checkpoints (func:afunction) =
  let version = active_version func in
  let instrs = version.instrs in

  (* Can only insert checkpoints into an unoptimized function *)
  if has_checkpoint instrs then None else

  let inp = Analysis.as_analysis_input func version in
  let scope = Scope.infer inp in

  let transform pc =
    let create_checkpoint pc =
      match scope.(pc) with
      | DeadScope -> Unchanged
      | Scope scope ->
        let vars = VarSet.elements scope in
        let varmap = List.map (fun x -> (x, (Simple (Var x)))) vars in
        let target = {
          func=func.name;
          version=version.label;
          pos=checkpoint_label pc;
        } in
        InsertBefore [Assume {label=checkpoint_label pc; guards=[]; target; varmap; extra_frames=[]};]
    in
    match[@warning "-4"] instrs.(pc) with
    | Label _ | Comment _ ->
        Unchanged
    | Assume _ -> assert false
    | _ -> create_checkpoint pc
  in
  let baseline = change_instrs transform inp in
  let (|?) opt def = match opt with Some v -> v | None -> def in
  Some { func with
         body = [
           { label = version.label;
             instrs = (|?) baseline instrs;
             annotations = None } ] }

module LabelTarget = struct
  type t = label position
  let compare = Pervasives.compare
end

module TargetSet = Set.Make(LabelTarget)

(* Removes all empty checkpoints with no incoming references *)
let remove_empty_checkpoints : opt_prog = fun prog ->
  let get_targets func version seen = function[@warning "-4"]
    | Assume {label; target; guards; extra_frames} ->
      let my_pos = { func = func.name; version = version.label; pos = label } in
      if guards <> [] || TargetSet.mem my_pos seen then begin
        let add tgs {cont_pos} = TargetSet.union tgs (TargetSet.singleton cont_pos) in
        List.fold_left add (TargetSet.singleton target) extra_frames
      end else TargetSet.empty
    | _ -> TargetSet.empty
  in
  let extract how what =
    let add tgs e = TargetSet.union tgs (how e) in
    List.fold_left add TargetSet.empty what
  in
  (* Collect the targets (including the extra frames continuations) of all non empty checkpoints.
   * This is a fixedpoint computation since even when there are no guards it might be a target itself
   * and thus need to be kept alive. *)
  let rec fixpoint_used seen =
    let used =
      extract (fun (f : afunction) ->
        extract (fun (v : version) ->
          extract (get_targets f v seen) (Array.to_list v.instrs)) f.body) (prog.main::prog.functions)
    in
    if TargetSet.equal used seen
    then used
    else fixpoint_used used
  in
  let used = fixpoint_used TargetSet.empty in

  let changed = ref false in

  let prog' =
    let apply func =
      let baseline = List.hd (List.rev func.body) in
      let body =
        List.map (fun version ->
          let inp = (Analysis.as_analysis_input func version) in
          let transform pc =
            let target pos = { func = func.name; version = version.label; pos = pos } in
            match[@warning "-4"] inp.instrs.(pc) with
            | Assume {guards; label}
                when guards = [] && not (TargetSet.mem (target label) used) -> Remove 1
            | Assume {guards; label}
                when guards = [] && version == baseline -> Replace [Label (BailoutLabel label)]
            | _ -> Unchanged
          in
          match change_instrs transform inp with
          | None -> version
          | Some instrs ->
              changed := true;
              { version with instrs }
        ) func.body
      in
      { func with body }
    in
    { main = apply prog.main;
      functions = List.map apply prog.functions; }
  in

  if !changed
  then Some prog'
  else None

(* Create a new version. This is a copy of the current one where all
 *    the bailout targets point one version down (ie. to the current one).
 *)
let create_new_version (func : afunction) : version =
  (* This takes the active version and duplicates it. Bailout targets are
   * updated to point to the currently active version *)
  let next_version (func:afunction) =
    let cur_version = Instr.active_version func in
    let inp = Analysis.as_analysis_input func cur_version in
    let scope = Scope.infer inp in
    let transform pc =
      match[@warning "-4"] cur_version.instrs.(pc) with
      | Assume {label;guards} ->
        begin match scope.(pc) with
        | DeadScope -> Remove 1
        | Scope scope ->
          let vars = VarSet.elements scope in
          let varmap = List.map (fun x -> (x, (Simple (Var x)))) vars in
          let target = {
            func=func.name;
            version=cur_version.label;
            pos=label;
          } in
          Replace [Assume {label; guards; target; varmap; extra_frames=[]};]
        end
      | _ -> Unchanged
    in
    let inp = Analysis.as_analysis_input func cur_version in
    { label = Edit.fresh_version_label func cur_version.label;
      instrs = (match change_instrs transform inp with | None -> cur_version.instrs | Some i -> i);
      annotations = None }
  in
  next_version func

(* Starting from pc walk up the cfg and find the earliest possible
 *    checkpoint for the guard. Branch targets are blocking as
 *    are instructions which interfere with the guard. The
 *    condition has to be added to an existing checkpoint instruction (see
 *    insert_checkpoints above). *)
let add_guard ?(hoist=false) (func : afunction) (version : version) cond pc : version option =
  let instrs = version.instrs in
  let preds = Analysis.predecessors instrs in
  (* Finds the highest up checkpoint in that basic block where the
   * assumption can be placed. *)
  let rec find_candidate cond_vars pc acc =
    if pc < 0 then acc else
    match[@warning "-4"] instrs.(pc) with
    | Assume _ ->
      if hoist
      then find_candidate cond_vars (pc-1) (Some pc)
      else Some pc
    | Label _ ->
      begin match[@warning "-4"] preds.(pc) with
      | [pred] -> find_candidate cond_vars pred acc
      | _ -> acc
      end
    | _ ->
      assert (preds.(pc) = [pc-1] || preds.(pc) = []);
      if preds.(pc) <> [] && Instr.independent instrs.(pc) cond
      then find_candidate cond_vars (pc-1) acc
      else acc
  in
  let vars = expr_vars cond in
  begin match find_candidate vars (pc-1) None with
  | None -> None
  | Some pc ->
    begin match[@warning "-4"] instrs.(pc) with
    | Assume ({guards} as def) ->
      instrs.(pc) <- Assume {def with guards=cond::guards};
      Some { version with instrs }
    | _ -> assert (false)
    end
  end

(* hoist_assumption tries to hoist assumptions out of loops.
 *
 * Like in insert_assumption the strategy is to find the earliest possible osr
 * instruction where a condition can be moved to and which ensures that the
 * condition still holds for the original position. In the most trivial case
 * this can be the following example
 *
 *   osr [x==1] ...
 *   print x
 *   osr [x==2] ...
 *   ===============>
 *   osr [x==1,x==2] ...
 *   print x
 *   osr []
 *
 * The interesting case is where hoist_assumption is able to move an assumption
 * out of a loop:
 *
 *    osr [] ...
 *    goto loop
 *   loop:
 *    print (x+1)
 *    osr [x==1] ...
 *    print x
 *    branch _ loop cont
 *   cont:
 *   ===================>
 *    osr [x==1] ...
 *    goto loop
 *   loop:
 *    print (x+1)
 *    osr [] ...
 *    print x
 *    branch _ loop cont
 *   cont:
 *
 * The condition to move an assumption over a multi-predecessor label is:
 * 1. There is an unique dominator
 * 2. On all other predecessors the assumption is already available.
 *
 * In the above example:
 * 0. We can move the assumption to `loop:` because `print (x+1)` is
 *    independent of x==1.
 * 1. There is an unique dominator (ie. the loop entry)
 * 2. On the other predecessor (ie. the branch instruction) the assumption
 *    is available because `print x` is independent of x==1.
 *)
let hoist_assumption : transform_instructions = fun ({instrs; _} as inp) ->
  let instrs = Array.copy instrs in
  let available = Analysis.valid_assumptions inp in
  let preds = Analysis.predecessors instrs in
  let dominates = Analysis.dominates inp in
  let rec find_candidates pc acc =
    if pc = Array.length instrs then acc else
    match[@warning "-4"] instrs.(pc) with
    | Assume {guards} when guards <> [] -> find_candidates (pc+1) (pc::acc)
    | _ -> find_candidates (pc+1) acc
  in
  let candidates = find_candidates 0 [] in

  (* Finds the highest up checkpoint that dominates this instruction
   * and where the intermediate instructions don't change the condition.
   * For multi-predecessor instruction we can push the assumption to a
   * unique dominator if the assumption is available on all other
   * predecessors. *)
  let rec find_candidate_cp cond cond_vars pc acc =
    if pc < 0 then acc else
    match[@warning "-4"] instrs.(pc) with
    | Assume _ -> find_candidate_cp cond cond_vars (pc-1) (Some pc)
    | Label _ ->
      let doms, rest = List.partition (fun pc' -> dominates pc' pc) preds.(pc) in
      begin match doms with
      | [dom] ->
        let all_guarded = List.for_all (fun pc' ->
            let available = available pc' in
            Analysis.ExpressionSet.mem cond available
          ) rest in
        if all_guarded
        then find_candidate_cp cond cond_vars dom acc
        else acc
      | _ -> acc
      end
    | _ ->
      assert (preds.(pc) = [pc-1] || preds.(pc) == []);
      if preds.(pc) <> [] && Instr.independent instrs.(pc) cond
      then find_candidate_cp cond cond_vars (pc-1) acc
      else acc
  in

  let changed = ref false in
  let push_guard pc =
    match[@warning "-4"] instrs.(pc) with
    | Assume ({guards} as def) ->
      let try_push c =
        let cond_vars = expr_vars c in
        begin match find_candidate_cp c cond_vars (pc-1) None with
        | None -> true
        | Some pc' ->
          changed := true;
          begin match[@warning "-4"] instrs.(pc') with
          | Assume ({guards} as def) ->
            instrs.(pc') <- Assume {def with guards = c :: guards}
          | _ -> assert (false)
          end;
          false
        end
      in
      let remaining = List.filter try_push guards in
      instrs.(pc) <- Assume {def with guards = remaining}
    | _ -> assert (false)
  in
  List.iter push_guard candidates;
  if !changed then Some instrs else None


let activate_assumptions ?(hoist=true) (func : afunction) : version option =
  let version = ref (create_new_version func) in
  let instrs = (!version).instrs in
  let rec find_assume pc =
    if pc = Array.length instrs then [] else
    match[@warning "-4"] instrs.(pc) with
    | Guard_hint (exps) ->
        let new_assumptions = List.map (fun exp -> pc, exp) exps in
        new_assumptions @ find_assume (pc+1)
    | _ -> find_assume (pc+1)
  in
  let assumes = find_assume 0 in
  List.iter (fun (pc, exp) ->
    match add_guard ~hoist:hoist func (!version) exp pc with
    | Some v -> version := v
    | None -> ()
  ) assumes;
  let instrs = (!version).instrs in
  let remove_assumes pc =
    match[@warning "-4"] instrs.(pc) with
    | Guard_hint _ -> Transform_utils.Remove 1
    | _ -> Transform_utils.Unchanged
  in
  match change_instrs remove_assumes (Analysis.as_analysis_input func {(!version) with instrs}) with
  | Some instrs -> Some {!version with instrs}
  | None -> None
