open Instr
open Transform_utils

let minimize_liverange ({formals; instrs} : analysis_input) : instructions option =
  let remove_drops instrs =
    Array.of_list (
      List.filter (fun x -> match[@warning "-4"] x with
          | Drop _ -> false | _ -> true)
        (Array.to_list instrs))
  in
  let instrs = remove_drops instrs in
  let inp = {formals; instrs} in
  let predecessors = Analysis.predecessors instrs in
  let required = Analysis.required_vars inp in
  let aliased = Analysis.aliased inp in
  let keep_alive pc = VarSet.union (VarSet.of_list (required pc)) (aliased pc) in
  let keep_alive = Analysis.saturate keep_alive inp in
  let keep_alive_before pc =
    (* It might seem like we need to take the union over all predecessors. But
     * since required_merged_vars_at extends lifetimes to mergepoints this is
     * equivalent to just look at the first predecessor *)
    match predecessors.(pc) with | [] -> VarSet.empty | p :: _ -> keep_alive p
  in
  let transform pc =
    let keep_alive = keep_alive pc in
    assert (pc < Array.length instrs);
    let keep_alive_before = keep_alive_before pc in
    let to_drop = VarSet.diff keep_alive_before keep_alive in
    let drops = List.map (fun x -> Drop x) (VarSet.elements to_drop) in
    if drops = []
    then Unchanged
    else Insert drops
  in
  change_instrs transform inp
