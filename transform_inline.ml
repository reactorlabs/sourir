open Instr
open Edit
open Types

type inlining_candidate = {
  pos : pc;
  target : afunction;
  ret : variable;
  args : argument list;
  extra_frames : extra_frame list option;
  next : inlining_site;
}
and inlining_site = {
  version : version;
  candidates : inlining_candidate list;
}

(* FUNCTION INLINING *)
(* Given a program, inline the functions in it to the maximum possible extent.
   Transitively recursive calls are inlined until they become self recursive.
   Self recursive callsites are not inlined. Intermediate inlined versions are
   stored in the caller. *)
let inline ?(max_inlinings=10) ?(max_depth=100) ?(max_size=1000) () ({main; functions} as orig_prog : program) : program option =

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
    let version = active_version func in
    if depth > max_depth || Array.length version.instrs > max_size
    then { version; candidates = []}
    else begin
      (* This step is absolutely crucial to make sure that all checkpoints refer to the
       * current scope *)
      let new_version = Transform_assumption.create_new_version func in
      let new_instrs = new_version.instrs in
      let inlinings = ref [] in
      (* This function takes the information of a callsite and a safepoint after it to
       * compute a combined checkpoint frames list for the inlinee. To this end the current
       * toplevel varmap has to be put into the extra frames list. *)
      let create_bailout_continuation top_frame call_var bailout_label =
        let pos = {
          func = func.name;
          version = version.label;  (* need OLD version here *)
          pos = bailout_label; } in
        { varmap = List.filter (fun v -> match v with | (x, _) -> x <> call_var) top_frame;
          cont_res = call_var;
          cont_pos = pos; }
      in
      let visit_instr pc =
        if List.length !inlinings < max_inlinings then begin
          assert (pc+1 < Array.length new_instrs);
          match[@warning "-4"] new_instrs.(pc) with
          | Call (x, (Simple (Constant (Fun_ref f))), es) ->
            if LabelSet.mem f seen then () else begin
              (* To be able to osr out of this call we need to have a var_map
               * after the call to reconstruct the caller environment and
               * to have a target label after the call to reconstruct the continuation. *)
              let extra_frames = (
                match[@warning "-4"] new_instrs.(pc+1) with
                  | Assume {label; varmap; extra_frames} ->
                    Some ((create_bailout_continuation varmap x label) :: extra_frames)
                  | _ -> None) in
              let seen = LabelSet.add f seen in
              let callee = lookup_fun orig_prog f in
              let next = compute_inline_order callee seen (depth+1) in
              let inlining = { pos = pc; target = callee; ret = x; args = es; extra_frames; next } in
              inlinings := inlining :: !inlinings
            end
          | _ -> ()
        end
      in
      for pc = 0 to (Array.length new_instrs) - 2 do
        visit_instr pc
      done;
      { version = new_version; candidates = !inlinings }
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
   *    assume t0 _ (f0,v0,t0) [frame0]  (f1,v1,t1) [frame1], (f2,v2,t2) [frame2]
   *
   * Then we want to extend foo's extra_frames list by the following list:
   *    (f0,v1,t0) [var res = $, frame0/res], (f1,v1,t1) [frame1], (f2,v2,t2) [frame2]
   *
   * This ensures that when the deoptimized foo returns it returns after the call with the call
   * stack identical to before the call and the result stored to res.
   * Note: in the target we create function and version are the current active version and
   *       not the original bailout target (ie. v1 in (f0,v1,t0) is not a typo).
   *
   * The list of extra frames is accumulated by compute_inlining_order
   * *)
  let fixup_extra_frames extra_frames' input inlinee_name fresh_label =
    let open Transform_utils in
    let fixup pc =
      match[@warning "-4"] input.instrs.(pc) with
      | Assume ({label; extra_frames} as def) ->
        (* Two functions might import the same bailout label, we need to freshen them.
         * This is valid since we created a new version, thus we are guaranteed to not be
         * an active bailout target. *)
        let label = fresh_label (inlinee_name^"_"^label) in
        let extra_frames = extra_frames @ extra_frames' in
        Replace [ Assume { def with label; extra_frames } ]
      | _ -> Unchanged
    in
    match change_instrs fixup input with
    | None -> input.instrs
    | Some instrs -> instrs
  in

  let apply_inlinings func inlinings =
    let updated = ref [] in
    let rec apply_inlinings func inlinings : version =
      let new_version = inlinings.version in
      let candidates = inlinings.candidates in
      if candidates = []
      then new_version
      else
        let instrs = new_version.instrs in
        let fresh_bailout_label = Edit.bailout_label_freshener instrs in
        let inp = Analysis.as_analysis_input func new_version in
        let fresh_label = Edit.label_freshener instrs in
        let get {target; next; pos; ret; args; extra_frames} =
          let apply next = if next.candidates = []
                           then active_version target
                           else apply_inlinings target next in
          let callee = Analysis.as_analysis_input target (apply next) in
          match has_checkpoint callee.instrs, extra_frames with
          | false, _ ->
            let inlinee = compose inp callee fresh_label ret args in
            (pos, 1, inlinee.instrs)
          | true, Some extra_frames ->
            let inlinee = compose inp callee fresh_label ret args in
            (pos, 1, fixup_extra_frames extra_frames inlinee target.name fresh_bailout_label)
          | true, None ->
            (* The callee needs to bailout but the caller does not have a safepoint
             * after the call. We can't do anything. *)
            (pos, 0, [| |])
        in
        let to_inline = List.map get inlinings.candidates in
        let instrs, _ = Edit.subst_many instrs to_inline in
        let new_version = { new_version with instrs } in
        if new_version.label <> (active_version func).label
        then updated := (func.name, new_version) :: !updated;
        new_version
    in
    let _ = apply_inlinings func inlinings in
    !updated
  in

  let inline_at func =
    let inline_order = compute_inline_order func LabelSet.empty 0 in
    (* If there are no caller-callee pairs to inline, return `None`, else return
       the completely inlined program *)
    if inline_order.candidates = []
    then None
    else
      let result = apply_inlinings func inline_order in
      if result = []
      then None
      else Some result
  in

  (* Starting from main inline all the way down *)
  match inline_at orig_prog.main with
  | None -> None
  | Some res ->
    let try_update func =
      match List.assoc func.name res with
      | exception Not_found -> func
      | vers ->
        { func with body = vers :: func.body }
    in
    let functions = List.map try_update orig_prog.functions in
    let main = try_update orig_prog.main in
    Some { main; functions }
