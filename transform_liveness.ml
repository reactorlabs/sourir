open Instr
open Transform_utils

let minimize_liverange (instrs : instruction_stream) : instruction_stream option =
  let remove_drops instrs =
    Array.of_list (
      List.filter (fun x -> match[@warning "-4"] x with
          | Drop _ -> false | _ -> true)
        (Array.to_list instrs))
  in
  let instrs = remove_drops instrs in
  let predecessors = Analysis.predecessors instrs in
  let required = Analysis.required_vars instrs in
  let required = Analysis.saturate required instrs in
  let required_before pc =
    (* It might seem like we need to take the union over all predecessors. But
     * since required_merged_vars_at extends lifetimes to mergepoints this is
     * equivalent to just look at the first predecessor *)
    match predecessors.(pc) with | [] -> VarSet.empty | p :: _ -> required p
  in
  let transform pc =
    let required = required pc in
    let required_before = required_before pc in
    let to_drop = VarSet.diff required_before required in
    let drops = List.map (fun x -> Drop x) (VarSet.elements to_drop) in
    if drops = []
    then Unchanged
    else Insert drops
  in
  change_instrs transform instrs
