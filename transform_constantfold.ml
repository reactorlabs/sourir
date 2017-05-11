open Instr

(*
 * Constant propagation. Takes a program `prog` and returns an updated stream.
 *
 * Finds all constant declarations of the form:
 *     var x = l
 * where `l` is a literal.
 *
 * Then, whenever `x` is used in an expression (while x is still in scope), it
 * is replaced by the literal `l`. Afterwards, the variable `x` is no longer
 * used, and the declaration can be removed by running `minimize_lifetimes`.
 *)
let const_prop ({formals; instrs} : analysis_input) : instructions option =
  (* Replaces the variable `x` with literal `l` in instruction `instr`. *)
  let replace x l instr =
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
    | Decl_var (y, e) ->
      assert (x <> y);
      Decl_var (y, replace e)
    | Decl_mut (y, Some e) ->
      assert (x <> y);
      Decl_mut (y, Some (replace e))
    | Decl_array (y, def) ->
      assert (x <> y);
      let def = match def with
        | Length e -> Length (replace e)
        | List es -> List (List.map replace es)
      in Decl_array (y, def)
    | Assign (y, e) ->
      Assign (y, replace e)
    | Array_assign (y, i, e) ->
      Array_assign (y, replace i, replace e)
    | Branch (e, l1, l2) -> Branch (replace e, l1, l2)
    | Print e -> Print (replace e)
    | Osr {cond; target; map} ->
      (* Replace all expressions in the osr environment. *)
      let map = List.map (fun osr_def ->
        match osr_def with
        | Osr_var (y, e) -> Osr_var (y, replace e)
        | Osr_mut (y, e) -> Osr_mut (y, replace e)
        | Osr_mut_ref (_y, _z) ->
          (* we disable replacing aliases (mut y = &z) even
             when the value of (z) is statically known
             as this actually pessimizes the code, adding
             an extra allocation *)
          osr_def
        | Osr_mut_undef y -> Osr_mut_undef y) map
      in
      let cond = List.map replace cond in
      Osr {cond; target; map}
    | Decl_mut (y, None)
    | Drop y
    | Clear y
    | Read y ->
      instr
    | Label _ | Goto _ | Comment _ -> instr in

  let module VarMap = Map.Make(Variable) in

  let module Approx = struct
    type t = Unknown | Value of value
    let equal a1 a2 = match a1, a2 with
      | Unknown, Unknown -> true
      | Unknown, Value _ | Value _, Unknown -> false
      | Value v1, Value v2 -> Eval.value_eq v1 v2
  end in

  (* for each instruction, what is the set of variables that are constant? *)
  let constants =
    let open Analysis in
    let open Approx in
    let merge pc cur incom =
      let merge_approx x mv1 mv2 = match mv1, mv2 with
        | None, _ | _, None ->
          failwith "scope error?"
        | Some Unknown, _ | _, Some Unknown -> Some Unknown
        | Some (Value v1), Some (Value v2) ->
          if Eval.value_eq v1 v2 then Some (Value v1) else Some Unknown
      in
      if VarMap.equal Approx.equal cur incom then None
      else Some (VarMap.merge merge_approx cur incom)
    in
    let update pc cur =
      match[@warning "-4"] instrs.(pc) with
      | Decl_var (x, Simple (Constant l))
      | Decl_mut (x, Some (Simple (Constant l)))
        ->
        VarMap.add x (Value l) cur
      | Decl_array (x, _) ->
        (* this case could be improved with approximation for arrays so
           that, eg., length(x) could be constant-folded *)
        VarMap.add x Unknown cur
      | Decl_var (x, _) | Decl_mut (x, _) ->
        VarMap.add x Unknown cur
      | Call (x, _, _) as call ->
        let mark_unknown (_, x) cur = VarMap.add x Unknown cur in
        cur
        |> ModedVarSet.fold mark_unknown (changed_vars call)
        |> VarMap.add x Unknown
      | Drop x ->
        VarMap.remove x cur
      | Array_assign (x, _, _) | Read x | Clear x ->
        assert (VarMap.mem x cur);
        (* the array case could be improved with approximation for
           arrays *)
        VarMap.add x Unknown cur
      | Assign (x, Simple (Constant l)) ->
        assert (VarMap.mem x cur);
        VarMap.add x (Value l) cur
      | Assign (x, _) ->
        VarMap.add x Unknown cur
      | ( Branch _ | Label _ | Goto _ | Return _
        | Print _ | Stop _ | Osr _ | Comment _)
        as instr ->
        begin
          assert (ModedVarSet.is_empty (changed_vars instr));
          assert (VarSet.is_empty (dropped_vars instr));
          assert (ModedVarSet.is_empty (defined_vars instr));
        end;
        cur
    in
    let initial_state =
      let add_formal (_, x) st = VarMap.add x Unknown st in
      ModedVarSet.fold add_formal formals VarMap.empty
    in
    Analysis.forward_analysis initial_state instrs merge update
  in

  let transform_instr pc instr =
    let consts = constants pc in
    let transform x approx instr =
      match approx with
      | Approx.Unknown -> instr
      | Approx.Value l -> replace x (Constant l) instr in
    VarMap.fold transform consts instr in

  let new_instrs = Array.mapi transform_instr instrs in
  if new_instrs = instrs
  then None
  else Some new_instrs

open Transform_utils

let make_constant (({formals; instrs} as inp) : analysis_input) : instructions option =
  let required = Analysis.required inp in
  let constant var pc =
    match instrs.(pc) with
    | Assign (x, _)
    | Drop x
    | Clear x
    | Read x
    | Array_assign (x, _, _)
      -> x <> var
    | Call (_, _, exp) ->
      let is_passed_by_val = function
        | Arg_by_ref x -> x <> var
        | Arg_by_val _ -> true
      in List.for_all is_passed_by_val exp
    | Decl_var (_, _)
    | Decl_array _
    | Decl_mut (_, _)
    | Return _
    | Branch (_, _, _)
    | Label _
    | Goto _
    | Print _
    | Stop _
    | Osr _
    | Comment _
      -> true
  in

  let changes = Array.map (fun _ -> Unchanged) instrs in
  let rec apply pc =
    if Array.length instrs = pc then () else
    match[@warning "-4"] instrs.(pc) with
    | Decl_mut (var, Some exp) ->
      let required = required pc in
      if Analysis.PcSet.for_all (constant var) required
      then begin
        let fixup pc =
          let fixup_instr pc = function[@warning "-4"]
            | Osr {cond; target; map} ->
              let fixup_def = function[@warning "-4"]
                | Osr_mut_ref (x, y) when var = y -> Osr_mut (x, Simple (Var var))
                | d -> d in
              changes.(pc) <- Replace (Osr {cond; target; map = List.map fixup_def map})
            | _ -> () in
          match[@warning "-4"] changes.(pc) with
          | Unchanged -> fixup_instr pc instrs.(pc)
          | Replace i -> fixup_instr pc i
          | _ -> assert(false)
        in
        (* all uses keep this variable constant:
         * 1. Change the declaration to const
         * 2. Fixup osr uses: We need to materialize the heap value on osr-out *)
        changes.(pc) <- Replace (Decl_var (var, exp));
        Analysis.PcSet.iter fixup required;
      end;
      apply (pc+1)
    | _ ->
      apply (pc+1)
  in
  let () = apply 0 in
  change_instrs (fun pc -> changes.(pc)) inp
