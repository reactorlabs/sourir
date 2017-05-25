open Instr
open Types

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
let hoist_assignment : transform_instructions = fun ({formals; instrs} as inp) ->
  let open Analysis in
  let reaching = reaching inp in
  let uses = uses inp in
  let dominates = dominates inp in
  let dominates_all_uses pc =
    PcSet.for_all (fun use -> dominates pc use) (uses pc) in
  let aliased = aliased inp in
  let aliased var pc = VarSet.mem var (aliased pc) in
  let rec find_possible_move pc =
    if pc = Array.length instrs then None
    else
      let pc' = pc + 1 in
      match[@warning "-4"] instrs.(pc) with
      | Assign (x, exp) ->
        if (not (dominates_all_uses pc)) || (aliased x pc) then find_possible_move pc'
        else
          let reaching_defs = reaching pc in
          let valid_move candidate =
            let dominate_me = PosSet.for_all (fun pos -> match pos with
                | Arg -> true
                | Instr pc -> dominates pc candidate) in
            dominates candidate pc && dominate_me reaching_defs in

          begin match find_first instrs valid_move with
          | exception Not_found -> find_possible_move pc'
          | pc' -> Some (pc, pc')
          end

      (* TODO: others? *)
      | i -> find_possible_move pc'
  in

  match find_possible_move 0 with
  | None -> None
  | Some (from_pc, to_pc) ->
    let copy = Array.copy instrs in
    Edit.freshen_assign {formals; instrs=copy} from_pc;
    Edit.move copy from_pc to_pc;
    Some copy
