open Instr

let const_prop instrs =
  let rec find_candidates instrs pc =
    if pc = Array.length instrs then [] else
    match[@warning "-4"] instrs.(pc) with
    | Decl_const (x, Simple(Lit(n))) ->
        (pc, x, n) :: find_candidates instrs (pc+1)
    | _ -> find_candidates instrs (pc+1)
  in

  let convert x n instr =
    let replace = Replace.var_in_exp x n in
    match instr with
    | Decl_const (y, e) ->
      assert (x <> y);
      Decl_const (y, replace e)
    | Decl_mut (y, Some e) ->
      assert (x <> y);
      Decl_mut (y, Some (replace e))
    | Assign (y, e) ->
      assert (x <> y);
      Assign (y, replace e)
    | Branch (e, l1, l2) -> Branch (replace e, l1, l2)
    | Print e -> Print (replace e)
    | Osr (exp, l1, l2, env) ->
      let env' = List.map (fun osr_def ->
        match[@warning "-4"] osr_def with
        | OsrConst (y, e) -> OsrConst (y, replace e)
        | _ -> osr_def) env
      in
      Osr (replace exp, l1, l2, env')
    | Drop y
    | Decl_mut (y, None)
    | Clear y
    | Read y ->
      assert (x <> y);
      instr
    | Label _ | Goto _ | Stop | Comment _ -> instr in

  let rec to_convert instrs worklist x acc =
    let open Analysis in
    match worklist with
    | [] -> acc
    | pc :: rest ->
      begin match[@warning "-4"] instrs.(pc) with
      | Drop y when x = y -> to_convert instrs rest x acc
      | instr ->
        let succs = successors_at instrs pc in
        if PcSet.mem pc acc then to_convert instrs rest x acc
        else to_convert instrs (succs @ rest) x (PcSet.add pc acc)
      end in

  let work instrs =
    let open Analysis in
    let candidates = find_candidates instrs 0 in
    let propagate instrs (pc, x, n) =
      let succs = successors_at instrs pc in
      let worklist = to_convert instrs succs x PcSet.empty in
      let instrs = Array.copy instrs in
      PcSet.iter (fun pc -> instrs.(pc) <- convert x (Lit(n)) instrs.(pc)) worklist;
      instrs
    in
    List.fold_left propagate instrs candidates in

  work instrs
