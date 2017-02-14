open Instr

let remove_empty_jmp (instrs : segment) : segment =
  let pred = Analysis.predecessors instrs in
  let succ = Analysis.successors instrs in
  let rec remove_empty_jmp pc acc : segment =
    let pc' = pc + 1 in
    if pc' = Array.length instrs then
      Array.of_list (List.rev (instrs.(pc) :: acc))
    else
      match[@warning "-4"] instrs.(pc), instrs.(pc') with
      | Goto l1, Label l2 when l1 = l2 && List.length pred.(pc') = 1 ->
        remove_empty_jmp (pc+2) acc
      | Label _, _ when pred.(pc) = [pc-1] && succ.(pc-1) = [pc] ->
          (* A label is unused if the previous instruction is the only predecessor
           * unless the previous instruction jumps to it. The later can happen
           * if its a goto (then we already remove it -- see above) or if its a branch (which
           * is excluded by the second tests "succ (pc-1) = [pc]")
           * TODO: we should implement some generic api for instructions like, "Instr.is_jmp" *)
        remove_empty_jmp pc' acc
      | i, _ ->
        remove_empty_jmp pc' (i::acc)
  in
  remove_empty_jmp 0 []

let remove_unreachable_code (instrs : segment) : segment =
  let unreachable =
    let merge _ _ _ = None in
    let update _ _ = () in
    Analysis.forward_analysis () instrs merge update
  in
  let rec remove_unreachable pc acc : segment =
    let pc' = pc+1 in
    if pc = Array.length instrs then
      Array.of_list (List.rev acc)
    else
      let i = instrs.(pc) in
      match unreachable pc with
      | exception Analysis.UnreachableCode _ ->
        remove_unreachable pc' acc
      | () ->
        remove_unreachable pc' (i::acc)
  in
  remove_unreachable 0 []

let branch_prune (prog : program) : program =
  let main = List.assoc "main" prog in
  let rest = List.remove_assoc "main" prog in
  let deopt_label = "main_" ^ string_of_int (List.length prog) in
  let scope = Scope.infer main in
  let live = Analysis.live main in
  let rec branch_prune pc acc =
    if pc = Array.length main then
      Array.of_list (List.rev acc)
    else
      match scope pc with
      | Scope.Dead -> assert(false)
      | Scope.Scope scope ->
        let pc' = pc + 1 in
        begin match[@warning "-4"] main.(pc) with
        | Branch (exp, l1, l2) ->
          let osr = List.map (function
              | (Const_var, x) ->
                OsrConst (x, (Simple (Var x)))
              | (Mut_var, x) ->
                if List.exists (fun x' -> x = x') (live pc) then
                  OsrMut (x, x)
                else
                  OsrMutUndef x)
              (ModedVarSet.elements scope)
          in
          branch_prune pc'
            (Goto l2 :: Osr (exp, deopt_label, l1, osr) :: acc)
        | i ->
          branch_prune pc' (i::acc)
        end
  in
  let final = branch_prune 0 [] in
  let cleanup = remove_empty_jmp (remove_unreachable_code final) in
  ("main", cleanup) :: (deopt_label, main) :: rest
