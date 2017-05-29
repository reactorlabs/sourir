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
    to a [Label label] instruction in [pc'].
*)
let split_edge instrs preds pc label pc' =
  assert (not (is_checkpoint_label label));
  assert (instrs.(pc') = Label label);
  let split_label = fresh_label instrs label in
  let add_split_edge =
    (pc', 0, [|
        Label split_label;
        Goto label;
      |]) in
  let fix_pred pred_pc =
    if pred_pc <> pc then begin
      (* this is not the pc to update with the split label;
         it may either be an explicit jump to the label,
         which needs no change, or an instruction right before
         the label without an explicit jump, which now needs an
         explicit jump as the instruction after it will change. *)
      match[@warning "-4"] instrs.(pred_pc) with
      | Goto _ | Branch _ -> []
      | instr -> [(pred_pc, 1, [| instr; Goto label |])]
    end else begin
      match[@warning "-4"] instrs.(pc) with
      | Branch (v, l1, l2) ->
        let fix l = if l = label then split_label else l in
        if not (l1 = label || l2 = label) then invalid_arg "split_edge";
        [(pc, 1, [| Branch (v, fix l1, fix l2) |])]
      | _ -> invalid_arg "split_edge"
    end
  in
  let substs = add_split_edge :: List.flatten (List.map fix_pred preds.(pc')) in
  subst_many instrs substs

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
