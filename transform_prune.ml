open Instr
open Types
open Transform_utils

let insert_branch_pruning_assumption (func : afunction) : version option =
  let version = Instr.active_version func in
  let instrs = version.instrs in
  (* Finds the first branch instruction in the stream *)
  let rec find_branch pc =
    if pc = Array.length instrs then None else
    match[@warning "-4"] instrs.(pc) with
    | Branch (exp, l1, l2) -> Some (pc, exp)
    | _ -> find_branch (pc+1)
  in
  match find_branch 0 with
  | None -> None
  | Some (pc, branch_cond) ->
    Transform_assumption.insert_assumption func branch_cond pc

let branch_prune : transform_instructions = fun input ->
  let assumptions = Analysis.valid_assumptions input in
  let rec find_candidates pc branches =
    if pc = Array.length input.instrs then branches else
    match[@warning "-4"] input.instrs.(pc) with
    | Branch (e, l1, l2) when Analysis.ExpressionSet.mem e (assumptions pc) ->
      (* This branch has to go to l2! *)
      find_candidates (pc+1) ((pc,l2)::branches)
    | _ ->
      find_candidates (pc+1) branches
  in
  let candidates = find_candidates 0 [] in
  let resolve = Instr.resolve input.instrs in
  let changes = List.map (fun (b_pc, l) ->
    [(b_pc, 1, [| Goto l |]);
     (* We also need to fix the label, since it's not a branch label anymore *)
     (resolve (BranchLabel l), 1, [| Label (MergeLabel l) |])]) candidates in
  if changes = []
  then None
  else
    let instrs, _ = Edit.subst_many input.instrs (List.flatten changes) in
    Some instrs
