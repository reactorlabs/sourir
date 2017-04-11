open Instr
open Transform_utils

let result_version (func : afunction) (label : label) (instrs : instruction_stream) : version =
  { label = Edit.fresh_version_label func label;
    instrs;
    annotations = None }

let insert_branch_pruning_assumption (func : afunction) : version option =
  let version = Instr.active_version func in
  let instrs = version.instrs in
  let scope = Scope.infer func version in
  let live = Analysis.live instrs in
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
                Osr_mut (x, x)
              else
                Osr_mut_undef x)
            (ModedVarSet.elements scope)
        in
        Insert [Osr (exp, func.name, version.label, l1, osr); Goto l2]
      | _ -> Unchanged
      end
  in
  match change_instrs transform instrs with
  | None -> None
  | Some instrs -> Some (result_version func version.label instrs)
