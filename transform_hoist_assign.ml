open Instr
open Types

let freshen_assign ({instrs} as inp : analysis_input) (def : pc) future_pos =
  let uses = Analysis.PcSet.elements (Analysis.uses inp def) in
  let instr = instrs.(def) in
  match[@warning "-4"] instr with
  | Assign (x, exp) ->
    let fresh = Edit.fresh_var instrs x in
    let all_changed = ref true in
    let open Transform_utils in
    let change_use pc =
      let open Analysis in
      (* Is there another reaching definition that defines the same
         variable? In that case we cannot replace this use by a read
         to the hoisted constant. *)
      let reaching_defs = reaching inp pc in
      let remaining_defs = PosSet.remove (Instr def) reaching_defs in
      let blocking = function
        | Arg -> false
        | Instr pc -> VarSet.mem x (defined_vars instrs.(pc)) in
      if PosSet.exists blocking remaining_defs
      then (all_changed := false; (pc, Unchanged))
      else (pc, Replace [(Edit.replace_uses x fresh)#instruction instrs.(pc)])
    in
    let changed_uses = List.map change_use uses in
    let fresh_decl = [Decl_var (fresh, exp)] in
    let fresh_assign =
      if !all_changed then [] else [Assign (x, Simple (Var fresh))] in
    let transform pc =
      if pc = def && pc = future_pos then Replace (fresh_decl @ fresh_assign)
      else if pc = def then Replace fresh_assign
      else if pc = future_pos then InsertBefore fresh_decl
      else try List.assoc pc changed_uses with Not_found -> Unchanged
    in
    Transform_utils.change_instrs transform inp
  | _ -> invalid_arg "freshen_assign"

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
 * Another concern is whether evaluating the rhs is allowed. For now we take
 * a conservative approach and only allow simple expressions.
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
        let is_simple = function[@warning "-4"]
          | Simple _ -> true
          | _ -> false in
        if (not (dominates_all_uses pc)) || (aliased x pc) || not (is_simple exp)
        then find_possible_move pc'
        else begin
          let reaching_defs = reaching pc in
          let valid_move candidate =
            match[@warning "-4"] instrs.(candidate) with
            | Label _ -> false
            | _ ->
              let dominate_me = PosSet.for_all (fun pos -> match pos with
                  | Arg -> true
                  | Instr pc -> dominates pc candidate) in
              dominates candidate pc &&
              dominate_me reaching_defs in

          begin match find_first instrs valid_move with
          | exception Not_found -> find_possible_move pc'
          | pc' -> Some (pc, pc')
          end
        end
      (* TODO: others? *)
      | i -> find_possible_move pc'
  in
  match find_possible_move 0 with
  | None -> None
  | Some (from_pc, to_pc) ->
      match freshen_assign inp from_pc to_pc with
      | Some instrs ->
          Transform_utils.fix_scope {formals; instrs}
      | None -> None
