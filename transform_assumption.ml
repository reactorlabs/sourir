open Instr
open Types
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
  let version = active_version func in
  let instrs = version.instrs in

  (* Can only insert checkpoints into an unoptimized function *)
  if has_osr instrs then None else

  let inp = Analysis.as_analysis_input func version in
  let scope = Scope.infer inp in

  let transform pc =
    let create_checkpoint pc =
      match scope.(pc) with
      | DeadScope -> Unchanged
      | Scope scope ->
        let vars = VarSet.elements scope in
        let osr = List.map (fun x -> Osr_var (x, (Simple (Var x)))) vars in
        let target = {
          func=func.name;
          version=version.label;
          pos=checkpoint_label pc;
        } in
        InsertBefore [Osr {label=checkpoint_label pc; cond=[]; target; varmap=osr; frame_maps=[]};]
    in
    match[@warning "-4"] instrs.(pc) with
    | Label _ | Comment _ ->
        Unchanged
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

module LabelTarget = struct
  type t = label position
  let compare = Pervasives.compare
end

module TargetSet = Set.Make(LabelTarget)

(* Removes all empty checkpoints with no incoming references *)
let remove_empty_osr : opt_prog = fun prog ->
  let get_targets = function[@warning "-4"]
    | Osr {target; cond; frame_maps} when cond <> [] ->
      let add tgs {cont_pos} = TargetSet.union tgs (TargetSet.singleton cont_pos) in
      List.fold_left add (TargetSet.singleton target) frame_maps
    | _ -> TargetSet.empty
  in
  let extract how what =
    let add tgs e = TargetSet.union tgs (how e) in
    List.fold_left add TargetSet.empty what
  in
  (* Collect the targets (including the extra frames continuations) of all non empty osrs *)
  let used =
    extract (fun (f : afunction) ->
      extract (fun (v : version) ->
        extract get_targets (Array.to_list v.instrs)) f.body) (prog.main::prog.functions)
  in

  (* Remove all empty and unused osr instructions in all versions *)
  let changed = ref false in

  let prog' =
    let apply func =
      let body =
        List.map (fun version ->
          let inp = (Analysis.as_analysis_input func version) in
          let transform pc =
            let target pos = { func = func.name; version = version.label; pos = pos } in
            match[@warning "-4"] inp.instrs.(pc) with
            | Osr {cond; label} when cond = [] && not (TargetSet.mem (target label) used) -> Remove 1
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

(* Inserts the assumption that osr_condition is false at position pc.
 * The approach is to
 * 1. Create a new version. This is a copy of the current one where all
 *    the osr targets point one version down (ie. to the current one).
 * 2. Starting from pc walk up the cfg and find the earliest possible
 *    checkpoint for the osr_condition. Branch targets are blocking as
 *    are instructions which interfere with the osr_condition. The
 *    condition has to be added to an existing osr instruction (see
 *    insert_checkpoints above). *)

let create_new_version (func : afunction) : version =
  (* This takes the active version and duplicates it. Osr targets are
   * updated to point to the currently active version *)
  let next_version (func:afunction) =
    let cur_version = Instr.active_version func in
    let transform pc =
      match[@warning "-4"] cur_version.instrs.(pc) with
      | Osr {label; cond; target; varmap; frame_maps} ->
        let target = {target with version = cur_version.label} in
        Replace [Osr {label; cond; target; varmap; frame_maps}]
      | _ -> Unchanged
    in
    let inp = Analysis.as_analysis_input func cur_version in
    { label = Edit.fresh_version_label func cur_version.label;
      instrs = (match change_instrs transform inp with | None -> cur_version.instrs | Some i -> i);
      annotations = None }
  in
  next_version func


let add_guard ?(hoist=false) (func : afunction) (version : version) osr_cond pc : version option =
  let instrs = version.instrs in
  let preds = Analysis.predecessors instrs in
  (* Finds the highest up osr checkpoint in that basic block where the
   * assumption can be placed. *)
  let rec find_candidate_osr cond_vars pc acc =
    if pc < 0 then acc else
    match[@warning "-4"] instrs.(pc) with
    | Osr _ ->
      if hoist
      then find_candidate_osr cond_vars (pc-1) (Some pc)
      else Some pc
    | Label _ ->
      begin match[@warning "-4"] preds.(pc) with
      | [pred] -> find_candidate_osr cond_vars pred acc
      | _ -> acc
      end
    | _ ->
      assert (preds.(pc) = [pc-1] || preds.(pc) = []);
      if preds.(pc) <> [] && Instr.independent instrs.(pc) osr_cond
      then find_candidate_osr cond_vars (pc-1) acc
      else acc
  in
  let osr_vars = expr_vars osr_cond in
  begin match find_candidate_osr osr_vars (pc-1) None with
  | None -> None
  | Some pc ->
    begin match[@warning "-4"] instrs.(pc) with
    | Osr {label; cond; target; varmap; frame_maps} ->
      instrs.(pc) <- Osr {label; cond=osr_cond::cond; target; varmap; frame_maps};
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
  let rec find_osrs pc acc =
    if pc = Array.length instrs then acc else
    match[@warning "-4"] instrs.(pc) with
    | Osr {cond} when cond <> [] -> find_osrs (pc+1) (pc::acc)
    | _ -> find_osrs (pc+1) acc
  in
  let osrs = find_osrs 0 [] in

  (* Finds the highest up osr checkpoint that dominates this instruction
   * and where the intermediate instructions don't change the condition.
   * For multi-predecessor instruction we can push the assumption to a
   * unique dominator if the assumption is available on all other
   * predecessors. *)
  let rec find_candidate_osr osr_cond cond_vars pc acc =
    if pc < 0 then acc else
    match[@warning "-4"] instrs.(pc) with
    | Osr _ -> find_candidate_osr osr_cond cond_vars (pc-1) (Some pc)
    | Label _ ->
      let doms, rest = List.partition (fun pc' -> dominates pc' pc) preds.(pc) in
      begin match doms with
      | [dom] ->
        let all_guarded = List.for_all (fun pc' ->
            let available = available pc' in
            Analysis.ExpressionSet.mem osr_cond available
          ) rest in
        if all_guarded
        then find_candidate_osr osr_cond cond_vars dom acc
        else acc
      | _ -> acc
      end
    | _ ->
      assert (preds.(pc) = [pc-1] || preds.(pc) == []);
      if preds.(pc) <> [] && Instr.independent instrs.(pc) osr_cond
      then find_candidate_osr osr_cond cond_vars (pc-1) acc
      else acc
  in

  let changed = ref false in
  let push_osr pc =
    match[@warning "-4"] instrs.(pc) with
    | Osr {label; cond; target; varmap; frame_maps} ->
      let try_push c =
        let cond_vars = expr_vars c in
        begin match find_candidate_osr c cond_vars (pc-1) None with
        | None -> true
        | Some pc' ->
          changed := true;
          begin match[@warning "-4"] instrs.(pc') with
          | Osr {label; cond; target; varmap; frame_maps} ->
            instrs.(pc') <- Osr {label; cond = c::cond; target; varmap; frame_maps}
          | _ -> assert (false)
          end;
          false
        end
      in
      let remaining = List.filter try_push cond in
      instrs.(pc) <- Osr {label; cond=remaining; target; varmap; frame_maps}
    | _ -> assert (false)
  in
  List.iter push_osr osrs;
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
