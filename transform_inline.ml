open Instr
open Edit
open Types

(* Unlike `analysis_input`, this preserves the order of `formals`. This
   facilitates matching the formals to the arguments passed at a callsite.*)
type inlining_input = {
  formals : variable list;
  instrs : instructions;
}

let as_inlining_input (func : afunction) : inlining_input =
  { formals = Analysis.as_var_list func.formals; instrs = (active_version func).instrs }

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
let inline ({main; functions} as orig_prog : program) : program option =

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
  let replace_vars caller ({formals; instrs} as callee) =
    let caller_vars = function_vars caller in
    let callee_vars = VarSet.elements (function_vars callee) in
    let replacements = Edit.fresh_many caller_vars callee_vars in
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
    let scope = Scope.infer {formals = VarSet.of_list callee.formals;
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
  let replace_labels used_labels ({formals; instrs} as callee) =
    let callee_labels = LabelSet.elements (extract_labels callee.instrs) in
    let replacements = Edit.fresh_many used_labels callee_labels in
    let mapper instr =
      let replace l = List.assoc l replacements in
      match[@warning "-4"] instr with
      | Label (MergeLabel l) -> Label (MergeLabel (replace l))
      | Label (BranchLabel l) -> Label (BranchLabel (replace l))
      | Goto l -> Goto (replace l)
      | Branch (e, l1, l2) -> Branch (e, replace l1, replace l2)
      | i -> i
    in
    let new_labels = LabelSet.of_list (snd (List.split replacements)) in
    {callee with instrs = Array.map mapper instrs}, LabelSet.union used_labels new_labels
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
  let compose caller callee used_labels ret_var arguments =
    let callee, used_labels = callee
                            |> replace_vars caller
                            |> replace_labels used_labels
    in
    (* It is important to generate return label and result variable after
       replacing variables and labels. Otherwise there is a good chance that
       they will not remain fresh. For ex - if `res` is present in both caller
       and callee, then `res_1` as a result variable will not remain fresh once
       `replace_vars` is called. Because `replace_vars` will replace `res` in
       callee with `res_1` and `res_1` is already used for the result variable.
       This problem will not happen if we `replace_vars` before generating a
       fresh `res_var`. *)
    let ret_lab = fresh used_labels "inl" in
    let used_labels = LabelSet.add ret_lab used_labels in

    let res_var =
      fresh (VarSet.union (function_vars callee) (function_vars caller)) "res"
    in
    let res = callee
            |> replace_returns res_var ret_lab
            |> insert_prologue res_var arguments
            |> insert_epilogue res_var ret_var ret_lab in
    (res, used_labels)
  in

  (* This function computes an order for inlining of the entire program.
     Given a call graph starting from main, it descends as deep as possible into
     the call chain and stops when it encounters an edge which leads to recursion.
  *)
  let rec compute_inline_order func seen : inlining_site =
    let instrs = (active_version func).instrs in
    let inlinings = ref [] in
    let visit_instr pc =
      assert (pc+1 < Array.length instrs);
      match[@warning "-4"] instrs.(pc) with
      | Call (x, (Simple (Constant (Fun_ref f))), es) ->
        if LabelSet.mem f seen then () else begin
          (* If the call is followed by a checkpoint we store it's
           * osr map to be able to concatenate it to the inlinee's *)
          let checkpoint = (match[@warning "-4"] instrs.(pc+1) with
                            | Osr {varmap; frame_maps} -> Some []
                            | _ -> None) in
          let seen = LabelSet.add f seen in
          let callee = lookup_fun orig_prog f in
          let next = compute_inline_order callee seen in
          let inlining = { pos = pc; target = callee; ret = x; args = es; osr = checkpoint; next } in
          inlinings := inlining :: !inlinings
        end
      | _ -> ()
    in
    for pc = 0 to (Array.length instrs) - 2 do
      visit_instr pc
    done;
    !inlinings
  in

  let needs_osr =
    let is_osr = function[@warning "-4"]
      | Osr _ -> true | _ -> false in
    Array.exists is_osr
  in

  let rec apply_inlinings func inlinings =
    let cur = as_inlining_input func in
    if inlinings = []
    then cur
    else
      let used_labels = ref (extract_labels cur.instrs) in
      let get {target; next; pos; ret; args; osr} =
        let apply next = if next = []
                         then as_inlining_input target
                         else apply_inlinings target next in
        let callee = apply next in
        match needs_osr callee.instrs, osr with
        | false, _ ->
            let inlinee, new_used = compose cur callee !used_labels ret args in
            used_labels := new_used;
            (pos, 1, inlinee.instrs)
        | true, Some osr ->
            (* TODO(osr): Here we need to update the inlinee osr points to create the
             *            additional osr frame. *)
            (pos, 0, [| |])
        | true , None ->
            (* The callee needs to osr but the caller does not have a safepoint
             * after the call. We can't do anything. *)
            (pos, 0, [| |])
      in
      let to_inline = List.map get inlinings in
      let instrs, _ = Edit.subst_many cur.instrs to_inline in
      { cur with instrs }
  in

  let inline_at func =
    let inline_order = compute_inline_order func LabelSet.empty in
    (* If there are no caller-callee pairs to inline, return `None`, else return
       the completely inlined program *)
    if inline_order = [] then None
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
