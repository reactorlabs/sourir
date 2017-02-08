open Instr

(* TODO:
    - keep track of const/mut status
*)

exception UndeclaredVariable of VarSet.t * pc
exception UninitializedVariable of VarSet.t * pc
exception DuplicateVariable of VarSet.t * pc

type scope_info = { declared : TypedVarSet.t; defined : TypedVarSet.t }
module ScopeInfo = struct
  type t = scope_info
  let inter a b = {declared = TypedVarSet.inter a.declared b.declared;
                   defined  = TypedVarSet.inter a.defined b.defined}
  let union a b = {declared = TypedVarSet.union a.declared b.declared;
                   defined  = TypedVarSet.union a.defined b.defined}
  let diff a b = {declared  = TypedVarSet.diff a.declared b.declared;
                   defined  = TypedVarSet.diff a.defined b.defined}
  let equal a b = TypedVarSet.equal a.declared b.declared &&
                  TypedVarSet.equal a.defined b.defined
end

(* Internally we keep track of the declared and defined variables.
 * The output scopes and the annotations contain only the declarations. But
 * internally infer asserts that undefined variables are never used and
 * declarations do not shadow a previous one
 *)
let infer (seg : segment) : inferred_scope array =
  let instructions = fst seg in
  let annotations = snd seg in
  let open Analysis in
  let merge cur incom =
    let merged = ScopeInfo.inter cur incom in
    if ScopeInfo.equal cur merged then None else Some merged in
  let update pc cur =
    let annot = annotations.(pc) in
    let instr = instructions.(pc) in
    let added = {
      declared = Instr.declared_vars instr;
      defined = Instr.defined_vars instr;
    } in
    let shadowed = TypedVarSet.inter cur.declared added.declared in
    if not (TypedVarSet.is_empty shadowed) then
      raise (DuplicateVariable (TypedVarSet.untyped shadowed, pc));
    let cur =
      { cur with
        declared = begin match annot with
          | None | Some (At_least _) -> cur.declared
          | Some (Exact constraints) ->
            TypedVarSet.inter_untyped cur.declared constraints
        end
      } in
    let updated = ScopeInfo.union cur added in
    { declared = TypedVarSet.diff_untyped updated.declared (Instr.dropped_vars instr);
      defined = TypedVarSet.diff_untyped updated.defined (Instr.cleared_vars instr)
    }
  in
  let initial_state = {declared = TypedVarSet.empty; defined = TypedVarSet.empty} in
  let res = Analysis.forward_analysis initial_state seg merge update in
  let finish pc res =
    let annotation = annotations.(pc) in
    let instr = instructions.(pc) in
    match res with
    | None -> Dead
    | Some res ->
      let must_have_declared vars =
        let declared = TypedVarSet.untyped res.declared in
        if not (VarSet.subset vars declared)
        then raise (UndeclaredVariable (VarSet.diff vars declared, pc)) in
      must_have_declared (Instr.required_vars instr);
      begin match annotation with
        | None -> ()
        | Some (At_least xs | Exact xs) -> must_have_declared xs;
      end;
      let must_have_defined vars =
        let defined = TypedVarSet.untyped res.defined in
        if not (VarSet.subset vars defined)
        then raise (UninitializedVariable (VarSet.diff vars defined, pc)) in
      must_have_defined (Instr.used_vars instr);
      Scope res.declared
  in
  Array.mapi finish res

