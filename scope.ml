open Instr

module VarSet = Set.Make(Variable)

(** TODO:
    - "none", how to handle ?
    - keep track of const/mut status
*)

let bound_vars = function
  | Decl_const (x, _)
  | Decl_mut (x, _) -> VarSet.singleton x
  | (Assign _
    | Branch _
    | Label _
    | Goto _
    | Print _
    | Invalidate _
    | Stop) -> VarSet.empty

let expr_vars = function
  | Var x -> VarSet.singleton x
  | Lit _ -> VarSet.empty
  | Op (_op, xs) -> VarSet.of_list xs

let free_vars = function
  | Decl_const (_x, e) -> expr_vars e
  | Decl_mut (_x, e) -> expr_vars e
  | Assign (x, e) -> VarSet.union (VarSet.singleton x) (expr_vars e)
  | Branch (e, _l1, _l2) -> expr_vars e
  | Label _l | Goto _l -> VarSet.empty
  | Print e -> expr_vars e
  | Invalidate (e, _l, xs) ->
    VarSet.union (VarSet.of_list xs) (expr_vars e)
  | Stop -> VarSet.empty

let successors program pc =
  let pc' = pc + 1 in
  let next = if pc' = Array.length program then [] else [pc'] in
  let resolve = Instr.resolve program in
  match program.(pc) with
  | Decl_const _
  | Decl_mut _
  | Assign _
  | Label _
  | Print _ -> next
  | Goto l | Invalidate (_, l, _) -> [resolve l]
  | Branch (_e, l1, l2) -> [resolve l1; resolve l2]
  | Stop -> []

let update cell set =
  match !cell with
  | None -> cell := Some set; Some set
  | Some old_set ->
    let new_set = VarSet.inter set old_set in
    cell := Some new_set;
    if VarSet.equal old_set new_set then None
    else Some new_set

exception UndefinedVariable of VarSet.t

let infer (program : instruction array) =
  let state =
    let temp instr = ref None, instr in
    Array.map temp program in
  let rec work = function
    | (set, pc) :: rest ->
      let (preset, instr) = state.(pc) in
      begin match update preset set with
      | None -> work rest
      | Some env ->
        let free, bound, succs =
          free_vars instr, bound_vars instr,
          successors program pc in
        let env' = VarSet.union bound env in
        let new_work = List.map (fun pc -> (env', pc)) succs in
        work (new_work @ rest)
      end
    | [] ->
      let finish (cell, instr) =
        let free = free_vars instr in
        match !cell with
        | Some set ->
            if not (VarSet.subset free set) then
              raise (UndefinedVariable (VarSet.diff free set));
            (set, instr)
        | None -> (VarSet.singleton "none", instr)
      in
      Array.map finish state
  in work [(VarSet.empty, 0)]
