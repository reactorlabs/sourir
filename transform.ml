open Instr

let remove_empty_jmp prog =
  let pred = Analysis.predecessors prog in
  let succ = Analysis.successors prog in
  let rec remove_empty_jmp pc =
    let pc' = pc + 1 in
    if pc' = Array.length prog then [prog.(pc)] else
      match[@warning "-4"] (prog.(pc), prog.(pc')) with
      | (Goto l1, Label l2) when l1 = l2 && List.length pred.(pc') = 1 ->
          remove_empty_jmp (pc+2)
      | (Label _, _) when pred.(pc) = [pc-1] && succ (pc-1) = [pc] ->
          (* A label is unused if the previous instruction is the only predecessor
           * unless the previous instruction jumps to it. The later can happen
           * if its a goto (then we already remove it -- see above) or if its a branch (which
           * is excluded by the second tests "succ (pc-1) = [pc]")
           * TODO: we should implement some generic api for instructions like, "Instr.is_jmp" *)
          remove_empty_jmp pc'
      | (_, _) ->
          prog.(pc) :: remove_empty_jmp pc'
  in
  remove_empty_jmp 0

let remove_dead_code prog entry=
  let dead_code =
    let merge _ _ = None in
    let update _ _ = () in
    Analysis.forward_analysis_from entry () prog merge update
  in
  let rec remove_dead_code pc =
    let pc' = pc+1 in
    if pc = Array.length prog then [] else
      match[@warning "-4"] dead_code.(pc), prog.(pc) with
      (* Comments are considered live, if the next instruction is live.
       * This prevents removing comments above jump labels *)
      | None, Comment c ->
          if pc' = Array.length prog then [] else
            begin match dead_code.(pc') with
            | None -> remove_dead_code pc'
            | Some _ -> Comment c :: remove_dead_code pc'
            end
      | None, _ -> remove_dead_code pc'
      | Some _, _ -> prog.(pc) :: remove_dead_code pc'
  in
  remove_dead_code 0

(* TODO: allow pruning of the true branch
 * we need to be able to negate expressions for that *)
let branch_prune (prog, scope) =
  let deopt_label l = "%deopt_" ^ l in
  (* Convert "branch e l1 l2" to "invalidate e l1; goto l2" *)
  let rec kill_branch pc =
    if pc = Array.length prog then [Stop] else
    match scope.(pc) with
    | Dead -> assert(false)
    | Scope scope ->
        begin match[@warning "-4"] prog.(pc) with
        | Branch (exp, l1, l2) ->
            let vars = Instr.VarSet.elements scope in
            Invalidate (exp, deopt_label l2, vars) ::
              Goto l1 ::
                kill_branch (pc+1)
        | i ->
            i :: kill_branch (pc+1)
        end
  in
  (* Scan the code and generate a landing-pad for all invalidates *)
  let gen_landing_pad entry =
    let rec gen_landing_pad pc =
      if pc = Array.length prog then [Stop] else
        let fresh_label l = l ^ "@" ^ entry in
        match prog.(pc) with
        (* this is the entry point, need to create the landing pad label *)
        | Label l when (deopt_label l) = entry ->
            Label (fresh_label l) ::
              Label entry :: gen_landing_pad (pc+1)
        (* we need to rename labels since they might clash with main function
         * TODO: this is ugly! what else should we do? *)
        | Label l ->
            Label (fresh_label l) :: gen_landing_pad (pc+1)
        | Goto l ->
            Goto (fresh_label l) :: gen_landing_pad (pc+1)
        | Branch (exp, l1, l2) ->
            Branch (exp, (fresh_label l1), (fresh_label l2)) :: gen_landing_pad (pc+1)
        | Invalidate _ -> assert(false)
        | (Decl_const _ | Decl_mut _ | Assign _
           | Read _ | Print _ | Stop | Comment _) as i ->
            i :: gen_landing_pad (pc+1)
    in
    let copy = Array.of_list (gen_landing_pad 0) in
    (* so far the landing pad is a copy of the original function. lets remove
     * the unreachable part of the prologue *)
    let continuation = remove_dead_code copy (resolve copy entry) in
    Array.of_list (Comment ("Landing pad for deopt " ^ entry) :: continuation)
  in
  let rec gen_deopt_targets = function[@warning "-4"]
    | Invalidate (exp, label, vars) :: rest ->
        gen_landing_pad label :: gen_deopt_targets rest
    | _ :: rest ->
        gen_deopt_targets rest
    | [] -> []
  in
  let killed = kill_branch 0 in
  let landing_pads = gen_deopt_targets killed in
  let final = Array.of_list killed in
  let combined = Array.concat (final :: landing_pads) in
  let cleanup = Array.of_list (remove_dead_code combined 0) in
  Array.of_list (remove_empty_jmp cleanup)
