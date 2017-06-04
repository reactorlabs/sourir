open Instr
open Edit

(* Unlike `analysis_input`, this preserves the order of `formals`. This
   facilitates matching the formals to the arguments passed at a callsite.*)
type inlining_input = {
  formals : variable list;
  instrs : instructions;
}

let as_inlining_input (func : afunction) (version : version) : inlining_input =
  { formals = Analysis.as_var_list func.formals; instrs = version.instrs }

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

  (* Given a function and an array of instructions, generate a fresh version
     for the function with these instructions. *)
  let add_version (func : afunction) (instrs : instructions)  =
    let label = fresh_version_label func "inlined_version" in
    let version = {instrs = instrs; label = label; annotations = None} in
    {func with body = version :: func.body}
  in

  (* Given `instructions` and the function identifier, extract the location,
     return variable and arguments from the first callsite where a call is made
     to that function *)
  let extract_callsite instrs fun_ref : (pc * variable * argument list) =
    let rec at pc =
      match[@warning "-4"] instrs.(pc) with
      | Call (x, (Simple (Constant (Fun_ref f))), es) ->
        if f = fun_ref then (pc, x, es) else at (pc + 1)
      | _ -> at (pc + 1)
    in
    at 0
  in

  (* Replace variables in `callee` instructions so that they don't match the
     `caller` variables. The formals list of the callee is also updated
     accordingly *)
  let replace_vars caller ({formals; instrs} as callee) =
    let caller_vars = function_vars caller in
    let callee_vars = function_vars callee in
    let replacements =
      List.map (fun old -> (old, fresh caller_vars old))
        (VarSet.elements callee_vars)
    in
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
  let replace_labels caller ({formals; instrs} as callee) =
    let used_labels = extract_labels caller.instrs in
    let replace l = fresh used_labels l in
    let mapper instr =
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
  let compose caller callee ret_var arguments : inlining_input =
    let callee = callee
                 |> replace_vars caller
                 |> replace_labels caller
    in
    (* It is important to generate return label and result variable after
       replacing variables and labels. Otherwise there is a good chance that
       they will not remain fresh. For ex - if `res` is present in both caller
       and callee, then `res_1` as a result variable will not remain fresh once
       `replace_vars` is called. Because `replace_vars` will replace `res` in
       callee with `res_1` and `res_1` is already used for the result variable.
       This problem will not happen if we `replace_vars` before generating a
       fresh `res_var`. *)
    let ret_lab =
      fresh_label (Array.append callee.instrs caller.instrs) "inl"
    in
    let res_var =
      fresh (VarSet.union (function_vars callee) (function_vars caller)) "res"
    in
    callee
    |> replace_returns res_var ret_lab
    |> insert_prologue res_var arguments
    |> insert_epilogue res_var ret_var ret_lab
  in

  (* Given the caller and callee identifiers, generate a fresh version of caller
     with the callee inlined.*)
  let inline_pair (caller_id : identifier)
                  (callee_id : identifier)
                  (prog : program) =
    let caller = lookup_fun prog caller_id in
    let caller' = as_inlining_input caller (List.hd caller.body) in
    let callee = lookup_fun prog callee_id in
    let callee' = as_inlining_input callee (List.hd callee.body) in
    let (pc, ret_var, arguments) = extract_callsite caller'.instrs callee_id in
    let callee'' = compose caller' callee' ret_var arguments in
    let instrs, _ = subst caller'.instrs pc 1 callee''.instrs in
    add_version caller instrs
  in

(* This function computes an order for inlining of the entire program.
   Given a call graph starting from main, it descends as deep as possible into
   the call chain and stops when it encounters an edge which leads to recursion.
   Using this depth-first approach, it generates all caller-callee pairs with
   the depth at which this pair was generated. This depth is used to sort the
   list of these pairs such that the inlining happens in a bottom up fashion.
   If a caller-callee pair is already encountered, then it is not included
   again. This is because once the callee has been inlined in the caller at a
   given callsite, then the callsite no longer exists. However, multiple
   callsites with the same target will result in as many caller-callee pairs.
   Note - The word reduced is used in the general sense of something being
   simplified. If a function has been analyzed for inlining, its considered
   reduced. In reality, inlining expands this function.
   The accumulator `acc` is composed of the following components -
   - `ord` - The list of (caller name, callee name, depth) triplets
   - `caller` - The caller object
   - `vis` - The set of visited function names
   - `red` - The set of reduced (already analyzed for inlining) function names
   - `dep` - The depth of this function from `main`
*)
  let compute_inlining_order (prog : program) : (identifier * identifier) list =
    let rec inspect_instr ((ord, caller, vis, red, dep) as acc) instr =
      match[@warning "-4"] instr with
      | Call (x, (Simple (Constant (Fun_ref f))), es) ->
        (* If `f` is already visited in this branch, then there is recursion,
           so don't add this pair to accumulator.*)
        if (VarSet.mem f vis) then acc
        (* If `f` is already analyzed for inlining, then add it but don't go
           inside it.*)
        else if (VarSet.mem f red)
        then ((caller.name, f, dep) :: ord, caller, vis, red, dep)
        (* If `f` is neither visited in this branch, nor has it been analyzed
           for inlining before, then descend into it and analyze it.*)
        else
          let callee = lookup_fun prog f in
          let (callee_ord, _, _, callee_red, _) =
            add_callees callee vis red (dep + 1)
          in
          let new_ord = (caller.name, f, dep) :: ord @ callee_ord in
          let new_red = VarSet.union red callee_red in
          (* Note that visited set is only maintained for a branch while
             reduced set is carried across branches. *)
          (new_ord, caller, vis, new_red, dep)
      (* Any other instruction returns accumulator unchanged. *)
      | _ -> acc
    and add_callees caller vis red dep =
      (* The `caller` is being visited and reduced. So add it to the two sets.*)
      let vis = VarSet.add caller.name vis in
      let red = VarSet.add caller.name red in
      Array.fold_left
        inspect_instr
        ([], caller, vis, red, dep)
        (List.hd caller.body).instrs
    in
    (* Sort (caller, callee, depth) triplets in decreasing order of depth. *)
    let comp (_, _, d1) (_, _, d2) = d2 - d1 in
    let (ord, _, _, _, _) = add_callees main VarSet.empty VarSet.empty 1 in
    List.map
      (fun (caller_id, callee_id, _ ) -> (caller_id, callee_id))
      (List.sort comp ord)
  in

  (* Given a list of caller - callee pairs, inline the callee inside the caller
     until the list is exhausted. Order matters, as only this order will result
     in a maximally inlined program excluding recursive calls. The final program
     will only have recursive calls left to be inlined. *)
  let inline_with order prog =
    List.fold_left
      (fun p (caller, callee) -> replace_fun p (inline_pair caller callee p))
      prog
      order
  in

  (* If there are no caller-callee pairs to inline, return `None`, else return
     the completely inlined program *)
  let inline_order = compute_inlining_order orig_prog in
  if List.length inline_order = 0 then None
  else Some (inline_with inline_order orig_prog)
