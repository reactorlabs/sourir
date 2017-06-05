open Instr
open Types

module StringSet = Set.Make(String)

let fresh (existing : StringSet.t) (name : string) : string =
  let cand i = name ^ "_" ^ (string_of_int i) in
  let is_fresh cand_var = not (StringSet.mem cand_var existing) in
  let rec find i =
    let cand_var = cand i in
    if is_fresh cand_var then cand_var else find (i+1) in
  find 1

let fresh_var instrs var =
  let existing = Array.fold_left
      (fun acc instr -> VarSet.union (declared_vars instr) acc)
      VarSet.empty instrs
  in
  fresh existing var

let extract_labels instrs =
  let add_label acc instr =
    match[@warning "-4"] instr with
    | Label (MergeLabel l | BranchLabel l) -> LabelSet.add l acc
    | _ -> acc
  in
  Array.fold_left add_label LabelSet.empty instrs

let fresh_label instrs label = fresh (extract_labels instrs) label

let fresh_version_label (func : afunction) label =
  let existing = List.map (fun {label} -> label) func.body in
  fresh (StringSet.of_list existing) label

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

let replace_uses old_name new_name = object (self)
  inherit Instr.map as super
  method! variable_use x =
    if x = old_name then new_name else x
end

let replace_var var simple_exp = object (self)
  inherit Instr.map as super
  method! simple_expression e = match e with
    | Constant _ -> e
    | Var x -> if x = var then simple_exp else e
end

let replace_all_vars replacements = object (self)
  inherit Instr.map as super
  method replace x = try List.assoc x replacements with Not_found -> x
  method! binder x = self#replace x
  method! variable_assign x = self#replace x
  method! variable_use x = self#replace x
end
