open Instr
open Types

(* TODO unify those 3 functions *)
let fresh_var instrs var =
  let cand i = var ^ "_" ^ (string_of_int i) in
  let is_fresh cand_var instr =
    let existing = declared_vars instr in
    not (VarSet.mem cand_var existing) in
  let rec find i =
    let cand_var = cand i in
    if Array.for_all (is_fresh cand_var) instrs then cand_var else find (i+1) in
  find 1

let fresh_label instrs label =
  let cand i = label ^ "_" ^ (string_of_int i) in
  let is_fresh cand_lab instr = match[@warning "-4"] instr with
    | Label l -> l <> cand_lab
    | _ -> true in
  let rec find i =
    let cand_lab = cand i in
    if Array.for_all (is_fresh cand_lab) instrs
    then cand_lab else find (i+1) in
  find 1

let fresh_version_label (func : afunction) label =
  let cand i = label ^ "_" ^ (string_of_int i) in
  let existing = List.map (fun {label} -> label) func.body in
  let rec find i =
    let cand_lab = cand i in
    if not (List.mem cand_lab existing)
    then cand_lab else find (i+1) in
  find 1

let move instrs from_pc to_pc =
  let (dir, to_pc) = if from_pc > to_pc then (-1, to_pc) else (1, to_pc-1) in
  let from = instrs.(from_pc) in
  let rec move pc =
    if pc <> to_pc then begin
      instrs.(pc) <- instrs.(pc+dir);
      move (pc+dir)
    end
  in
  move from_pc;
  instrs.(to_pc) <- from

type pc_map = int -> int

type result = Instr.instructions * pc_map

let subst_pc instrs start_pc len new_instrs pc =
  if pc < start_pc then pc
  else pc - len + Array.length new_instrs

let subst instrs pc len new_instrs =
  Array.concat [
    Array.sub instrs 0 pc;
    new_instrs;
    Array.sub instrs (pc + len) (Array.length instrs - pc - len);
  ], subst_pc instrs pc len new_instrs

let subst_many instrs substs =
  let rec chunks cur_pc substs =
    let chunk_upto pos = Array.sub instrs cur_pc (pos - cur_pc) in
    match substs with
    | (next_pc, len, insert_instrs) :: rest ->
      if next_pc < cur_pc then invalid_arg "subst_many";
      let rest, pc_map = chunks (next_pc + len) rest in
      let pc_map pc =
        subst_pc instrs next_pc len insert_instrs (pc_map pc)
      in
      let instrs = chunk_upto next_pc :: insert_instrs :: rest in
      instrs, pc_map
    | [] -> [chunk_upto (Array.length instrs)], fun pc -> pc
  in
  let compare (pc1, _, _) (pc2, _, _) =
    if pc1 = pc2 then invalid_arg "subst_many";
    Pervasives.compare (pc1 : int) pc2 in
  let instrs, pc_map = chunks 0 (List.sort compare substs) in
  Array.concat instrs, pc_map

(** [split_edge instrs pc label pc']
    splits the edge from a branch instruction in [pc]
    to a [Label label] instruction in [pc'],
    assuming there is no fallthrough to [pc'] -- all
    other predecessors are gotos or branches.

    Before applying it to arbitrary program, we use
    [Transform.remove_fallthroughs_to_label] to make the
    assumption hold.
*)
let split_edge instrs pc label pc' =
  assert (not (is_checkpoint_label label));
  assert (instrs.(pc') = Label label);
  let split_label = fresh_label instrs label in
  let split_edge = [|
    Label split_label;
    Goto label;
  |] in
  (* insert the split edge *)
  let new_instrs, pc_map = subst instrs pc' 0 split_edge in
  let new_branch = match[@warning "-4"] instrs.(pc) with
    | Branch (v, l1, l2) ->
      if l1 = label
      then Branch (v, split_label, l2)
      else if l2 = label
      then Branch (v, l1, split_label)
      else invalid_arg "split_edge"
    | _ -> invalid_arg "split_edge" in
  new_instrs.(pc_map pc) <- new_branch;
  new_instrs, pc_map

let replace_uses old_name new_name = object (self)
  inherit Instr.map as super
  method! variable_use x =
    if x = old_name then new_name else x
end

let freshen_assign ({instrs} as inp : analysis_input) (def : pc) =
  let uses = Analysis.PcSet.elements (Analysis.uses inp def) in
  let instr = instrs.(def) in
  match[@warning "-4"] instr with
  | Assign (x, exp) ->
    let fresh = fresh_var instrs x in
    instrs.(def) <- Decl_var (fresh, exp);
    let fix_use pc =
      instrs.(pc) <- (replace_uses x fresh)#instruction instrs.(pc) in
    List.iter fix_use uses;
  | _ ->
    assert(false)

let replace_var var simple_exp = object (self)
  inherit Instr.map as super
  method! simple_expression e = match e with
    | Constant _ -> e
    | Var x -> if x = var then simple_exp else e
end
