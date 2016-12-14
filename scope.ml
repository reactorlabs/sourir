open Instr

module VarSet = Set.Make(Variable)

type scope_annotation =
  | Exact of VarSet.t
  | At_least of VarSet.t

type inferred_scope =
  | Dead
  | Scope of VarSet.t

type annotated_program = (program * scope_annotation option array)

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

exception UndefinedVariable of VarSet.t

let infer (program : annotated_program) : inferred_scope array =
  let instructions = fst program in
  let annotations = snd program in
  let init_state = VarSet.empty in
  let merge cur in_set =
    let merged = VarSet.inter cur in_set in
    if VarSet.equal cur merged then None else Some merged in
  let update pc set =
    let annot = annotations.(pc) in
    let instr = instructions.(pc) in
    let constr_set =
      begin match annot with
      | None | Some (At_least _) -> set
      | Some (Exact vars) -> VarSet.inter set vars
      end in
    let bound = bound_vars instr in
    VarSet.union bound constr_set in
  let res = Analysis.forward_analysis init_state merge update instructions in
  let finish pc preset =
    let annotation = annotations.(pc) in
    let instr = instructions.(pc) in
    match preset with
    | None -> Dead
    | Some set ->
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
  Array.mapi finish res

