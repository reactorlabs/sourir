open Instr

let remove_empty_jmp (seg : segment) : segment =
  let instrs = fst seg in
  let annots = snd seg in
  let pred = Analysis.predecessors instrs in
  let succ = Analysis.successors instrs in
  let rec remove_empty_jmp pc acc_i acc_a : segment =
    let pc' = pc + 1 in
    if pc' = Array.length instrs then
      let acc_i, acc_a = instrs.(pc) :: acc_i, annots.(pc) :: acc_a in
      (Array.of_list (List.rev acc_i), Array.of_list (List.rev acc_a))
    else
      match[@warning "-4"] instrs.(pc), instrs.(pc'), annots.(pc) with
      | Goto l1, Label l2, a when l1 = l2 && List.length pred.(pc') = 1 ->
        remove_empty_jmp (pc+2) acc_i acc_a
      | Label _, _, a when pred.(pc) = [pc-1] && succ (pc-1) = [pc] ->
          (* A label is unused if the previous instruction is the only predecessor
           * unless the previous instruction jumps to it. The later can happen
           * if its a goto (then we already remove it -- see above) or if its a branch (which
           * is excluded by the second tests "succ (pc-1) = [pc]")
           * TODO: we should implement some generic api for instructions like, "Instr.is_jmp" *)
        remove_empty_jmp pc' acc_i acc_a
      | i, _, a ->
        remove_empty_jmp pc' (i::acc_i) (a::acc_a)
  in
  remove_empty_jmp 0 [] []

let remove_unreachable_code (seg : segment) entry : segment =
  let unreachable_code =
    let merge _ _ _ = None in
    let update _ _ = () in
    Analysis.forward_analysis_from entry () seg merge update
  in
  let instrs = fst seg in
  let annots = snd seg in
  let rec remove_unreachable_code pc acc_i acc_a : segment =
    let pc' = pc+1 in
    if pc = Array.length instrs then
      (Array.of_list (List.rev acc_i), Array.of_list (List.rev acc_a))
    else
      match unreachable_code.(pc), instrs.(pc), annots.(pc) with
      | None,   _, _ -> remove_unreachable_code pc' acc_i acc_a
      | Some _, i, a -> remove_unreachable_code pc' (i::acc_i) (a::acc_a)
  in
  remove_unreachable_code 0 [] []

let branch_prune (prog : program) : program =
  let main = List.assoc "main" prog in
  let rest = List.remove_assoc "main" prog in
  let deopt_label = "main_" ^ string_of_int (List.length prog) in
  let instrs = fst main in
  let annots = snd main in
  let scope = Scope.infer (fst main) in
  let live = Analysis.live main in
  let rec branch_prune pc acc_i acc_a =
    if pc = Array.length instrs then
      (Array.of_list (List.rev acc_i), Array.of_list (List.rev acc_a))
    else
      match scope.(pc) with
      | Dead -> assert(false)
      | Scope scope ->
        let pc' = pc + 1 in
        begin match[@warning "-4"] instrs.(pc), annots.(pc) with
        | Branch (exp, l1, l2), a ->
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
            (Goto l2 :: Osr (exp, deopt_label, l1, osr) :: acc_i)
            (None :: a :: acc_a)
        | i, a ->
          branch_prune pc' (i::acc_i) (a::acc_a)
        end
  in
  let final = branch_prune 0 [] [] in
  let cleanup = remove_empty_jmp (remove_unreachable_code final 0) in
  ("main", cleanup) :: (deopt_label, main) :: rest
