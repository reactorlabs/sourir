open Instr

let remove_empty_jmp prog =
  let pred = Analysis.predecessors prog in
  let rec remove_empty_jmp pc =
    let pc' = pc + 1 in
    if pc' = Array.length prog then [prog.(pc)] else
      match (prog.(pc), prog.(pc')) with
      | (Goto l1, Label l2) when l1 = l2 && List.length pred.(pc') = 1 ->
          remove_empty_jmp (pc+2)
      | (_, _) ->
          prog.(pc) :: remove_empty_jmp (pc')
  in
  let cleaned = remove_empty_jmp 0 in
  Array.of_list cleaned

let remove_dead_code prog entry=
  let dead_code =
    let init_state = ((), entry) in
    let merge _ _ = None in
    let update _ _ = () in
    Analysis.forward_analysis [init_state] prog merge update
  in
  let rec remove_dead_code pc =
    if pc = Array.length prog then [] else
      match dead_code.(pc), prog.(pc) with
      | None, Comment c -> Comment c :: remove_dead_code (pc+1)
      | None, _ -> remove_dead_code (pc+1)
      | Some _, _ -> prog.(pc) :: remove_dead_code (pc+1)
  in
  Array.of_list (remove_dead_code 0)

(* TODO: allow pruning of the true branch, but we need not expression for that *)
let branch_prune (prog, scope) =
  let deopt_label l = "%deopt_" ^ l in
  (* Convert "branch e l1 l2" to "invalidate e l1; goto l2" *)
  let rec kill_branch pc =
    if pc = Array.length prog then [Stop] else
    match scope.(pc) with
    | Scope.Dead -> assert(false)
    | Scope.Scope scope ->
        begin match prog.(pc) with
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
        (* we need to rename lables since they might clash with main function
         * TODO: this is ugly! what else should we do? *)
        | Label l ->
            Label (fresh_label l) :: gen_landing_pad (pc+1)
        | Goto l ->
            Goto (fresh_label l) :: gen_landing_pad (pc+1)
        | Branch (exp, l1, l2) ->
            Branch (exp, (fresh_label l1), (fresh_label l2)) :: gen_landing_pad (pc+1)
        | Invalidate _ -> assert(false)
        | i ->
            i :: gen_landing_pad (pc+1)
    in
    let instrs = Comment ("Landing pad for deopt " ^ entry) ::
      gen_landing_pad 0 in
    let copy = Array.of_list instrs in
    (* so far the landing pad is a copy of the original function. lets remove
     * the unreachable part of the prologue *)
    remove_dead_code copy (resolve copy entry)
  in
  let rec gen_deopt_targets = function
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
  remove_empty_jmp (remove_dead_code combined 0)


