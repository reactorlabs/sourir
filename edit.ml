let move instrs from_pc to_pc =
  let (dir, to_pc) = if from_pc > to_pc then (-1, to_pc) else (1, to_pc-1) in
  let from = instrs.(from_pc) in
  let rec move pc =
    if pc != to_pc then begin
      instrs.(pc) <- instrs.(pc+dir);
      move (pc+dir)
    end
  in
  move from_pc;
  instrs.(to_pc) <- from

let subst instrs pc len new_instrs =
  Array.concat [
    Array.sub instrs 0 pc;
    new_instrs;
    Array.sub instrs (pc + len) (Array.length instrs - pc - len);
  ]

let subst_pc instrs start_pc len new_instrs pc =
  if pc < start_pc then pc
  else pc - len + Array.length new_instrs

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
