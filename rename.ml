open Instr

let fresh_var instrs var =
  let cand i = var ^ "_" ^ (string_of_int i) in
  let is_fresh cand_var instr =
    let existing = ModedVarSet.untyped (declared_vars instr) in
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

let in_simple_expression old_name new_name (exp:simple_expression) : simple_expression =
  match exp with
  | Lit _ -> exp
  | Var x -> if x = old_name then Var new_name else exp

let in_expression old_name new_name exp : expression =
  let in_simple_expression = in_simple_expression old_name new_name in
  match exp with
  | Simple se -> Simple (in_simple_expression se)
  | Op (op, exps) ->
    Op (op, List.map in_simple_expression exps)

let in_osr old_name new_name osr : osr_def =
  let in_expression = in_expression old_name new_name in
  match osr with
  | OsrConst (x, exp) -> OsrConst (x, in_expression exp)
  | OsrMut (x, y) -> if y = old_name then OsrMut (x, new_name) else osr
  | OsrMutUndef _ -> osr

let uses_in_instruction old_name new_name instr : instruction =
  let in_expression = in_expression old_name new_name in
  let in_osr = in_osr old_name new_name in
  match instr with
  | Decl_const (x, exp) ->
    assert(x != old_name);   (* -> invalid scope *)
    Decl_const (x, in_expression exp)
  | Decl_mut (x, Some exp) ->
    assert (x != old_name);
    Decl_mut (x, Some (in_expression exp))
  | Assign (x, exp) ->
    Assign (x, in_expression exp)
  | Drop x ->
    if x = old_name then Drop new_name else instr
  | Clear x ->
    if x = old_name then Clear new_name else instr
  | Print exp ->
    Print (in_expression exp)
  | Branch (exp, l1, l2) ->
    Branch (in_expression exp, l1, l2)
  | Osr (exp, v, l, osrs) ->
    Osr (in_expression exp, v, l,
         List.map in_osr osrs)

  | Decl_mut (x, None)
  | Read x ->
    assert (x != old_name);
    instr

  | Label _ | Goto _ | Stop | Comment _ ->
    assert (VarSet.is_empty (used_vars instr));
    instr

let freshen_assign (instrs : segment) (def : pc) =
  let uses = Analysis.PcSet.elements (Analysis.used instrs def) in
  let instr = instrs.(def) in
  match[@warning "-4"] instr with
  | Assign (x, exp) ->
    let fresh = fresh_var instrs x in
    instrs.(def) <- Decl_mut (fresh, Some exp);
    List.iter (fun pc ->
      instrs.(pc) <- uses_in_instruction x fresh instrs.(pc)) uses
  | _ ->
    assert(false)
