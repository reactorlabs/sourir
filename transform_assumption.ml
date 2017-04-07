open Instr
open Transform_utils

let result_version (func : afunction) (label : label) (instrs : instructions) : version =
  { label = Edit.fresh_version_label func label;
    instrs;
    annotations = None }

let insert_branch_pruning_assumption (func : afunction) : version option =
  let version = Instr.active_version func in
  let instrs = version.instrs in
  let inp = Analysis.as_analysis_input func version in
  let scope = Scope.infer inp in
  let live = Analysis.live inp in
  let transform pc =
    match scope.(pc) with
    | DeadScope -> assert(false)
    | Scope scope ->
      begin match[@warning "-4"] instrs.(pc) with
      | Branch (exp, l1, l2) ->
        let osr = List.map (function
            | (Const_var, x) ->
              Osr_const (x, (Simple (Var x)))
            | (Mut_var, x) ->
              if List.mem x (live pc) then
                Osr_mut_ref (x,  x)
              else
                Osr_mut_undef x)
            (ModedVarSet.elements scope)
        in
        let target = { func=func.name; version=version.label; label=l1 } in
        Insert [Osr {cond=[exp]; target; map=osr}; Goto l2]
      | _ -> Unchanged
      end
  in
  match change_instrs transform inp with
  | None -> None
  | Some instrs -> Some (result_version func version.label instrs)
