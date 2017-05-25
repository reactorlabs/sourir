open Instr
open Types
open Transform_utils

let (insert_returns : transform_instructions) = fun {formals; instrs} ->
  let stops = Analysis.stops instrs in
  let add_return pc =
    if not (List.mem pc stops) then Unchanged
    else match[@warning "-4"] instrs.(pc) with
    | Return _ | Stop _ -> Unchanged
    | _ -> InsertAfter [Return (Simple (Constant Nil))]
  in Transform_utils.change_instrs add_return {formals; instrs}

let transform_with_prepass ~prepass transform = fun input ->
  let input = match prepass input with
    | None -> input
    | Some instrs -> {input with instrs} in
  transform input

let add_drops : transform_instructions =
  let add_drops ({formals; instrs} as input) =
    (* assume [insert_returns] has run *)
    let scope = Scope.infer input in
    let stops = Analysis.stops instrs in
    let add_drops pc =
      if not (List.mem pc stops) then Unchanged
      else match[@warning "-4"] instrs.(pc) with
        | (Return _ | Stop _) as instr ->
          begin match scope.(pc) with
            | DeadScope -> Unchanged
            | Scope scope ->
              let to_keep = required_vars instr in
              let to_drop = VarSet.diff scope to_keep in
              let drops =
                to_drop
                |> VarSet.elements
                |> List.map (fun x -> Drop x) in
              Insert drops
          end
        | _ -> assert false
    in
    Transform_utils.change_instrs add_drops input
  in
  transform_with_prepass ~prepass:insert_returns add_drops

let minimize_liverange : transform_instructions =
  transform_with_prepass ~prepass:add_drops Transform_hoist.Drop.apply
