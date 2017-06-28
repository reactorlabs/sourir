open Instr
open Edit
open Types

type inlining_candidate = {
  pos : pc;
  target : afunction;
  ret : variable;
  args : argument list;
  osr : osr_frame_map list option;
  next : inlining_site;
}
and inlining_site = inlining_candidate list

(* FUNCTION INLINING *)
(* Given a program, inline the functions in it to the maximum possible extent.
   Transitively recursive calls are inlined until they become self recursive.
   Self recursive callsites are not inlined. Intermediate inlined versions are
   stored in the caller. *)
let inline ?(max_depth=100) ?(max_size=1000) () ({main; functions} as orig_prog : program) : program option =

  (* Given the formals and instructions of a function, get all the declared and
     used vars in the function. *)
  let function_vars {formals; instrs} =
    let all_declared_vars instrs = Array.fold_left
        (fun vars instr -> VarSet.union vars (declared_vars instr))
        VarSet.empty
        instrs
    in
    (* This union is needed in case a formal is not used in the instructions. *)
    VarSet.union (all_declared_vars instrs) (VarSet.of_list formals)
  in

  (* Replace variables in `callee` instructions so that they don't match the
     `caller` variables. The formals list of the callee is also updated
     accordingly *)
  let existing_vars = ref VarSet.empty in
  let fresh_var var =
    let next = Edit.fresh_one (!existing_vars) var in
    existing_vars := StringSet.add next !existing_vars;
    next
  in
  let replace_vars caller ({formals; instrs} as callee) =
    let caller_vars = function_vars caller in
    existing_vars := StringSet.union !existing_vars caller_vars;
    let callee_vars = VarSet.elements (function_vars callee) in
    let replacements = fresh_many fresh_var callee_vars in
    {formals = List.map (fun var -> List.assoc var replacements) formals;
     instrs = Array.map (replace_all_vars replacements)#instruction instrs;}
  in

  (* Redirect all returns in the `callee` to a unique label (inserted later at
     the end of the callee's body) after assigning the return expression to a
     designated `res_var` and dropping all the variables in scope. *)
  let replace_returns res_var ret_lab ({formals; instrs} as callee) =
    let extract_returns instrs : (pc * expression) list =
      let rec loop pc acc =
        if pc = Array.length instrs then acc
        else match[@warning "-4"] instrs.(pc) with
          | Return e -> loop (pc + 1) ((pc, e) :: acc)
          | _ -> loop (pc + 1) acc
      in
      loop 0 []
    in
    let scope = Scope.infer {formals = callee.formals;
                             instrs = callee.instrs;}
    in
    let returns = extract_returns instrs in
    let subst_returns (pc, e) =
      match scope.(pc) with
      | DeadScope ->
        (* If it is dead scope, it remains dead scope even after this
           substitution. This replacement is done for the sake of consistency
           and clarity of inlined output. *)
        (pc, 1, [|Assert (Simple (Constant (Bool false)));
                  Assign (res_var, e);
                  Goto ret_lab |])
      | Scope varset ->
        let varlist = VarSet.elements varset in
        let drop_instrs = List.map (fun var -> Drop var) varlist in
        let new_instrs = Array.of_list ([Assign (res_var, e)]
                                        @ drop_instrs
                                        @ [Goto ret_lab]) in
        (pc, 1, new_instrs)
    in
    let substs = List.map subst_returns returns in
    {callee with instrs = fst (subst_many instrs substs)}
  in

  (* Replace labels in `callee` instructions so that they don't match the
     `caller` labels *)
  let replace_labels fresh_label ({formals; instrs} as callee) =
    let callee_labels = LabelSet.elements (extract_labels callee.instrs) in
    let replacements = fresh_many fresh_label callee_labels in
    let mapper instr =
      let replace l = List.assoc l replacements in
      match[@warning "-4"] instr with
      | Label (MergeLabel l) -> Label (MergeLabel (replace l))
      | Label (BranchLabel l) -> Label (BranchLabel (replace l))
      | Goto l -> Goto (replace l)
      | Branch (e, l1, l2) -> Branch (e, replace l1, replace l2)
      | i -> i
    in
    {callee with instrs = Array.map mapper instrs}
  in

  (* Inserts the header for the inlined callee body. Assigns all the formals to
     the arguments and initializes `res_var` to `nil`*)
  let insert_prologue res_var arguments ({formals; instrs} as callee) =
    let vars = Array.of_list (res_var :: formals) in
    let args = Array.of_list ((Simple (Constant Nil)) :: arguments) in
    let new_instrs = Array.map2 (fun x e -> Decl_var (x, e)) vars args in
    {callee with instrs = fst (subst instrs 0 0 new_instrs)}
  in

  (* Inserts the footer for the inlined callee body. Assigns the computed result
     to `ret_var` and drops the `res_var` *)
  let insert_epilogue res_var ret_var ret_lab ({formals; instrs} as callee) =
    let new_instrs = [|Label (MergeLabel ret_lab);
                       Decl_var (ret_var, (Simple (Var res_var)));
                       Drop res_var|]
    in
    {callee with
     instrs = fst (subst instrs (Array.length instrs) 0 new_instrs)}
  in

  (* Transforms the callee instructions to a form that can be substituted
     inside the caller.*)
  let compose caller callee (fresh_label : string -> string) ret_var arguments =
    let callee = callee
                 |> replace_vars caller
                 |> replace_labels fresh_label
    in
    (* It is important to generate return label and result variable after
       replacing variables and labels. Otherwise there is a good chance that
       they will not remain fresh. For ex - if `res` is present in both caller
       and callee, then `res_1` as a result variable will not remain fresh once
       `replace_vars` is called. Because `replace_vars` will replace `res` in
       callee with `res_1` and `res_1` is already used for the result variable.
       This problem will not happen if we `replace_vars` before generating a
       fresh `res_var`. *)
    let ret_lab = fresh_label "inl" in
    let res_var = fresh_var "res" in

    callee
    |> replace_returns res_var ret_lab
    |> insert_prologue res_var arguments
    |> insert_epilogue res_var ret_var ret_lab
  in

  (* This function computes an order for inlining of the entire program.
     Given a call graph starting from main, it descends as deep as possible into
     the call chain and stops when it encounters an edge which leads to recursion.
  *)
  let rec compute_inline_order func seen depth : inlining_site =
    let version = (active_version func) in
    let instrs = version.instrs in
    if depth = max_depth || Array.length instrs > max_size
    then []
    else begin
      let inlinings = ref [] in
      (* This function takes the information of a callsite and a safepoint after it to
       * compute a combined osr frames list for the inlinee. To this end the current
       * toplevel varmap has to be put into the extra frames list. *)
      let create_osr_continuation top_frame call_var osr_label =
        let pos = {
          func = func.name;
          version = version.label;
          pos = osr_label; } in
        { varmap = List.filter (fun v -> match v with | Osr_var (x, _) -> x <> call_var) top_frame;
          cont_res = call_var;
          cont_pos = pos; }
      in
      let visit_instr pc =
        assert (pc+1 < Array.length instrs);
        match[@warning "-4"] instrs.(pc) with
        | Call (x, (Simple (Constant (Fun_ref f))), es) ->
          if LabelSet.mem f seen then () else begin
            (* To be able to osr out of this call we need to have a var_map
             * after the call to reconstruct the caller environment and
             * to have a target label after the call to reconstruct the continuation. *)
            let checkpoint = (
              match[@warning "-4"] instrs.(pc+1) with
                | Osr {label; varmap; frame_maps} ->
                  Some ((create_osr_continuation varmap x label) :: frame_maps)
                | _ -> None) in
            let seen = LabelSet.add f seen in
            let callee = lookup_fun orig_prog f in
            let next = compute_inline_order callee seen (depth+1) in
            let inlining = { pos = pc; target = callee; ret = x; args = es; osr = checkpoint; next } in
            inlinings := inlining :: !inlinings
          end
        | _ -> ()
      in
      for pc = 0 to (Array.length instrs) - 2 do
        visit_instr pc
      done;
      !inlinings
    end
  in

  (* Update safepoints of the callee.
   * Given we want to inline the deopt information of the caller has to be
   * appended to the callee.
   *
   * If the call was followed by the following safepoint:
   *  version v1:
   *    ...
   *    call res = foo _
   *    osr t0 _ (f0,v0,t0) [frame0]  (f1,v1,t1) [frame1], (f2,v2,t2) [frame2]
   *
   * Then we want to extend foo's extra_frames list by the following list:
   *    (f0,v1,t0) [var res = $, frame0/res], (f1,v1,t1) [frame1], (f2,v2,t2) [frame2]
   *
   * This ensures that when the deoptimized foo returns it returns after the call with the call
   * stack identical to before the call and the result stored to res.
   * Note: in the target we create function and version are the current active version and
   *       not the original osr target (ie. v1 in (f0,v1,t0) is not a typo).
   *
   * The list of extra osr frames is accumulated by compute_inlining_order
   * *)
  let fixup_osr extra_frames input fresh_label =
    let open Transform_utils in
    let fixup_osr pc =
      match[@warning "-4"] input.instrs.(pc) with
      | Osr ({label; frame_maps} as osr) ->
        Replace [ Osr {osr with label = fresh_label label;
                       frame_maps = frame_maps @ extra_frames} ]
      | _ -> Unchanged
    in
    match change_instrs fixup_osr input with
    | None -> input.instrs
    | Some instrs -> instrs
  in

  let rec apply_inlinings func inlinings =
    let cur = Analysis.as_analysis_input func (active_version func) in
    if inlinings = []
    then cur
    else
      let fresh_bailout_label = Edit.bailout_label_freshener cur.instrs in
      let fresh_label = Edit.label_freshener cur.instrs in
      let get {target; next; pos; ret; args; osr} =
        let apply next = if next = []
                         then Analysis.as_analysis_input target (active_version target)
                         else apply_inlinings target next in
        let callee = apply next in
        match has_osr callee.instrs, osr with
        | false, _ ->
          let inlinee = compose cur callee fresh_label ret args in
          (pos, 1, inlinee.instrs)
        | true, Some osr ->
          let inlinee = compose cur callee fresh_label ret args in
          (pos, 1, fixup_osr osr inlinee fresh_bailout_label)
        | true, None ->
          (* The callee needs to osr but the caller does not have a safepoint
           * after the call. We can't do anything. *)
          (pos, 0, [| |])
      in
      let to_inline = List.map get inlinings in
      let instrs, _ = Edit.subst_many cur.instrs to_inline in
      { cur with instrs }
  in

  let inline_at func =
    let inline_order = compute_inline_order func LabelSet.empty 0 in
    (* If there are no caller-callee pairs to inline, return `None`, else return
       the completely inlined program *)
    if inline_order = []
    then None
    else
      let result = apply_inlinings func inline_order in
      let label = fresh_version_label func "inlined_version" in
      Some { label; annotations = None; instrs = result.instrs }
  in

  (* Starting from main inline all the way down *)
  match inline_at orig_prog.main with
  | None -> None
  | Some v ->
    Some { orig_prog with
      main = { orig_prog.main with
        body = v :: orig_prog.main.body
      }
    }
