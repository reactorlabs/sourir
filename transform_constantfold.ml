open Instr

(*
 * Constant propagation. Takes a program `prog` and returns an updated stream.
 *
 * Finds all constant declarations of the form:
 *     const x = l
 * where `l` is a literal.
 *
 * Then, whenever `x` is used in an expression (while x is still in scope), it
 * is replaced by the literal `l`. Afterwards, the variable `x` is no longer
 * used, and the declaration can be removed by running `minimize_lifetimes`.
 *)
let const_prop ({formals; instrs} : analysis_input) : instructions option =
  (* Finds the declarations that can be used for constant propagation.
     Returns a list of (pc, x, l) where `const x = l` is defined at pc `pc`. *)
  let rec find_candidates instrs pc acc =
    if pc = Array.length instrs then acc
    else match[@warning "-4"] instrs.(pc) with
    | Decl_const (x, Simple(Constant(l))) ->
        find_candidates instrs (pc+1) ((pc, x, l) :: acc)
    | _ -> find_candidates instrs (pc+1) acc
  in

  (* Replaces the variable `x` with literal `l` in instruction `instr`. *)
  let convert x l instr =
    let replace = Edit.replace_var_in_exp x l in
    let replace_arg = Edit.replace_var_in_arg x l in
    match instr with
    | Call (y, f, es) ->
      assert (x <> y);
      Call (y, replace f, List.map replace_arg es)
    | Stop e ->
      Stop (replace e)
    | Return e ->
      Return (replace e)
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
    | Osr (exp, f, v, l, env) ->
      (* Replace all expressions in the osr environment. *)
      let env' = List.map (fun osr_def ->
        match[@warning "-4"] osr_def with
        | Osr_const (y, e) -> Osr_const (y, replace e)
        | _ -> osr_def) env
      in
      Osr (replace exp, f, v, l, env')
    | Drop y
    | Decl_mut (y, None)
    | Clear y
    | Read y ->
      assert (x <> y);
      instr
    | Label _ | Goto _ | Comment _ -> instr in

  (* Finds the target pcs to perform constant propagation. *)
  let rec find_targets instrs x worklist acc =
    let open Analysis in
    match worklist with
    | [] -> acc
    | pc :: rest ->
      begin match[@warning "-4"] instrs.(pc) with
      | Drop y when x = y ->
        (* `x` is now out of scope, but continue searching the `rest` of the
           worklist. *)
        find_targets instrs x rest acc
      | instr ->
        if PcSet.mem pc acc then
          (* Already seen this pc, but continue searching the `rest` of the
             worklist. *)
          find_targets instrs x rest acc
        else
          (* Add the current `pc` to the accumulator and update the worklist
             with our successors. *)
          let succs = successors_at instrs pc in
          find_targets instrs x (succs @ rest) (PcSet.add pc acc)
      end
  in

  (* Perform constant propagation. *)
  let work instrs =
    let open Analysis in
    (* Find all constant propagation candidates. *)
    let candidates = find_candidates instrs 0 [] in
    if candidates = [] then None else
    (* Perform all propagations for a single candidate. *)
    let propagate instrs (pc, x, l) =
      let succs = successors_at instrs pc in
      let targets = find_targets instrs x succs PcSet.empty in
      let instrs = Array.copy instrs in
      let convert_at pc = instrs.(pc) <- convert x (Constant(l)) instrs.(pc) in
      PcSet.iter convert_at targets;
      instrs
    in
    Some (List.fold_left propagate instrs candidates)
  in

  work instrs
