open Instr

module VarSet = Set.Make(Variable)

type scope_annotation =
  | Exact of VarSet.t
  | At_least of VarSet.t

type inference_state =
  | Any_scope
  | Precise_scope of VarSet.t

type inferred_scope =
  | Dead
  | Scope of VarSet.t

(* TODO:
    - keep track of const/mut status
*)

let bound_vars = function
  | Decl_const (x, _)
  | Decl_mut (x, _) -> VarSet.singleton x
  | (Assign _
    | Branch _
    | Label _
    | Goto _
    | Read _
    | Print _
    | Invalidate _
    | Comment _
    | Stop) -> VarSet.empty

let expr_vars = function
  | Var x -> VarSet.singleton x
  | Lit _ -> VarSet.empty
  | Op (_op, xs) -> VarSet.of_list xs

let free_vars = function
  | Decl_const (_x, e) -> expr_vars e
  | Decl_mut (_x, e) -> expr_vars e
  | Assign (x, e) -> VarSet.union (VarSet.singleton x) (expr_vars e)
  | Branch (e, _l1, _l2) -> expr_vars e
  | Label _l | Goto _l -> VarSet.empty
  | Comment _ -> VarSet.empty
  | Read x -> VarSet.singleton x
  | Print e -> expr_vars e
  | Invalidate (e, _l, xs) ->
    VarSet.union (VarSet.of_list xs) (expr_vars e)
  | Stop -> VarSet.empty

let successors program pc =
  let pc' = pc + 1 in
  let next = if pc' = Array.length program then [] else [pc'] in
  let resolve = Instr.resolve program in
  match program.(pc) with
  | Decl_const _
  | Decl_mut _
  | Assign _
  | Label _
  | Comment _
  | Read _
  | Print _
    -> next
  | Goto l | Invalidate (_, l, _) -> [resolve l]
  | Branch (_e, l1, l2) -> [resolve l1; resolve l2]
  | Stop -> []

let update cell set =
  match !cell with
  | Any_scope -> cell := Precise_scope set; Some set
  | Precise_scope old_set ->
    let new_set = VarSet.inter set old_set in
    cell := Precise_scope new_set;
    if VarSet.equal old_set new_set then None
    else Some new_set

exception UndefinedVariable of VarSet.t

let infer annotated_program =
  let annotations = Array.map fst annotated_program in
  let program = Array.map snd annotated_program in
  let state = Array.map (fun _ -> ref Any_scope) annotated_program in
  let rec work = function
    | (set, pc) :: rest ->
      let set = match annotations.(pc) with
        | None | Some (At_least _) -> set
        | Some (Exact vars) -> VarSet.inter set vars in
      begin match update state.(pc) set with
      | None -> work rest
      | Some env ->
        let instr = program.(pc) in
        let free, bound, succs =
          free_vars instr, bound_vars instr,
          successors program pc in
        let env' = VarSet.union bound env in
        let new_work = List.map (fun pc -> (env', pc)) succs in
        work (new_work @ rest)
      end
    | [] ->
      let finish (annotation, instr) preset =
        match !preset with
        | Any_scope -> Dead
        | Precise_scope set ->
            let must_have vars =
              if not (VarSet.subset vars set)
              then raise (UndefinedVariable (VarSet.diff vars set)) in
            must_have (free_vars instr);
            begin match annotation with
              | None -> ()
              | Some (At_least xs | Exact xs) -> must_have xs;
            end;
            Scope set
      in
      Array.map2 finish annotated_program state
  in
  work [(VarSet.empty, 0)]
