open Instr
open Transform_utils

let remove_jmp (instrs : instruction_stream) : instruction_stream option =
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
  change_instrs transform instrs

let remove_unreachable_code (instrs : instruction_stream) : instruction_stream option =
  let unreachable =
    let merge _ _ _ = None in
    let update _ _ = () in
    Analysis.forward_analysis () instrs merge update
  in
  let transform pc =
    match unreachable pc with
    | exception Analysis.UnreachableCode _ -> Remove 1
    | () -> Unchanged
  in
  change_instrs transform instrs

let remove_unused_label (instrs : instruction_stream) : instruction_stream option =
  let rec loop pc acc =
    if pc >= Array.length instrs then acc
    else match[@warning "-4"] instrs.(pc-1), instrs.(pc) with
    | Goto _, Label _
    | Branch _, Label _ ->
      loop (pc+1) acc
    | _, Label l ->
      let edit = (pc, 0, [| Goto l |]) in
      loop (pc+1) (edit :: acc)
    | _, _ ->
      loop (pc+1) acc
  in
  let edits = loop 1 [] in
  if edits = []
  then None
  else Some (fst (Edit.subst_many instrs edits))

let remove_unused_decl (instrs : instruction_stream) : instruction_stream option =
  let open Analysis in
  let required = Analysis.required instrs in
  let used = Analysis.used instrs in
  let transform pc =
    match[@warning "-4"] instrs.(pc) with
    | Decl_mut (x, _)
    | Decl_const (x, _) when PcSet.is_empty (required pc) ->
      Remove 1
    | Assign _ when PcSet.is_empty (used pc) ->
      Remove 1
    | _ ->
      Unchanged
  in
  change_instrs transform instrs
