open Instr
open Transform_utils

let remove_jmp ({instrs} as inp : analysis_input) : instructions option =
  let pred = Analysis.predecessors instrs in
  let succ = Analysis.successors instrs in
  let transform pc =
    if (pc+1) = Array.length instrs then Unchanged else
    match[@warning "-4"] instrs.(pc), instrs.(pc+1) with
    | Goto l1, Label l2 when l1 = l2 && List.length pred.(pc+1) = 1 ->
      Remove 2
    | Label _, _ when pred.(pc) = [pc-1] && succ.(pc-1) = [pc] ->
        (* A label is unused if the previous instruction is the only predecessor
         * unless the previous instruction jumps to it. The later can happen
         * if its a goto (then we already remove it -- see above) or if its a branch (which
         * is excluded by the second tests "succ (pc-1) = [pc]")
         * TODO: we should implement some generic api for instructions like, "Instr.is_jmp" *)
      Remove 1
    | i, _ ->
      Unchanged
  in
  change_instrs transform inp

let remove_unreachable_code ({instrs} as inp : analysis_input) : instructions option =
  let reachable =
    let merge _ _ _ = None in
    let update _ _ = () in
    Analysis.forward_analysis () instrs merge update
  in
  let transform pc =
    match reachable pc with
    | exception Analysis.UnreachableCode _ -> Remove 1
    | () -> Unchanged
  in
  change_instrs transform inp

let remove_unused_decl ({instrs} as inp : analysis_input) : instructions option =
  let open Analysis in
  let required = Analysis.required inp in
  let used = Analysis.used inp in
  let aliased = Analysis.aliased inp in
  let aliased var pc = VarSet.mem var (aliased pc) in
  let transform pc =
    match[@warning "-4"] instrs.(pc) with
    | Decl_mut (x, _)
    | Decl_const (x, _) when PcSet.is_empty (required pc) ->
      Remove 1
    | Assign (x, _) when PcSet.is_empty (used pc) && not (aliased x pc) ->
      Remove 1
    | _ ->
      Unchanged
  in
  change_instrs transform inp
