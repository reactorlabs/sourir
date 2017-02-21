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
      match scope.(pc) with
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

let move instrs from_pc to_pc =
  let (dir, to_pc) = if from_pc > to_pc then (-1, to_pc) else (1, to_pc-1) in
  let from = instrs.(from_pc) in
  let rec move pc =
    if pc != to_pc then begin
      instrs.(pc) <- instrs.(pc+dir);
      move (pc+dir)
    end
  in
  move from_pc;
  instrs.(to_pc) <- from

(* Hoisting assignments "x <- exp" as far up the callgraph as possible.
 *
 * Since we are not in SSA moving assignments is only possible (without further
 * analysis) if the assignments dominates all its uses. Otherwise we might
 * accidentally capture uses on some traces.
 *
 * The condition for a move to be valid is that the move target dominates the
 * move origin (ie. we are moving upwards) and is dominated by all reaching
 * defs (ie. we are not moving above our dependencies).
 *
 * We only look at our own use-def chain. Thus the transformation renames the
 * variable to avoid overriding unrelated uses of the same name.
 *)
let hoist_assignment prog =
  let main = List.assoc "main" prog in
  let rest = List.remove_assoc "main" prog in
  let reaching = Analysis.reaching main in
  let uses = Analysis.used main in
  let dominates = Analysis.dominates main in
  let dominates_all_uses pc =
    Analysis.PcSet.for_all (fun use -> dominates pc use) (uses pc) in
  let rec find_possible_move pc =
    if pc = Array.length main then None
    else
      let pc' = pc + 1 in
      match[@warning "-4"] main.(pc) with
      | Assign (x, exp) ->
        if not (dominates_all_uses pc) then find_possible_move pc'
        else
          let reaching_defs = reaching pc in
          let valid_move candidate =
            let dominate_me = Analysis.PcSet.for_all (fun pc -> dominates pc candidate) in
            dominates candidate pc && dominate_me reaching_defs in

          begin match Analysis.find_first main valid_move with
          | exception Not_found -> find_possible_move pc'
          | pc' -> Some (pc, pc')
          end

      (* TODO: others? *)
      | i -> find_possible_move pc'
  in

  match find_possible_move 0 with
  | None -> prog
  | Some (from_pc, to_pc) ->
    let copy = Array.copy main in
    Rename.freshen_assign copy from_pc;
    move copy from_pc to_pc;
    ("main", copy) :: rest
