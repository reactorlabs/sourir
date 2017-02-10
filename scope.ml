open Instr

(* TODO:
    - keep track of const/mut status
*)

exception UndeclaredVariable of VarSet.t * pc
exception UninitializedVariable of VarSet.t * pc
exception DuplicateVariable of VarSet.t * pc

type scope_info = { declared : ModedVarSet.t; defined : ModedVarSet.t }
module ScopeInfo = struct
  type t = scope_info
  let inter a b = {declared = ModedVarSet.inter a.declared b.declared;
                   defined  = ModedVarSet.inter a.defined b.defined}
  let union a b = {declared = ModedVarSet.union a.declared b.declared;
                   defined  = ModedVarSet.union a.defined b.defined}
  let diff a b = {declared  = ModedVarSet.diff a.declared b.declared;
                   defined  = ModedVarSet.diff a.defined b.defined}
  let equal a b = ModedVarSet.equal a.declared b.declared &&
                  ModedVarSet.equal a.defined b.defined
end

exception IncompatibleScope of scope_info * scope_info

(* Internally we keep track of the declared and defined variables.
 * The output scopes and the annotations contain only the declarations. But
 * internally infer asserts that undefined variables are never used and
 * declarations do not shadow a previous one
 *)
let infer (seg : segment) : inferred_scope array =
  let instructions = fst seg in
  let annotations = snd seg in
  let open Analysis in
  let merge _pc cur incom =
    if ScopeInfo.equal cur incom
    then None
    else raise (IncompatibleScope (cur, incom)) in
  let update pc cur =
    let annot = annotations.(pc) in
    let instr = instructions.(pc) in
    let added = {
      declared = Instr.declared_vars instr;
      defined = Instr.defined_vars instr;
    } in
    let shadowed = ModedVarSet.inter cur.declared added.declared in
    if not (ModedVarSet.is_empty shadowed) then
      raise (DuplicateVariable (ModedVarSet.untyped shadowed, pc));
    let cur =
      { cur with
        declared = begin match annot with
          | None | Some (At_least _) -> cur.declared
          | Some (Exact constraints) ->
            ModedVarSet.inter_untyped cur.declared constraints
        end
      } in
    let updated = ScopeInfo.union cur added in
    let dropped, cleared = Instr.dropped_vars instr, Instr.cleared_vars instr in
    (* dropped variables must also be undefined, to preserve the property
       that only declared variables are defined. *)
    { declared = ModedVarSet.diff_untyped updated.declared dropped;
      defined = ModedVarSet.diff_untyped updated.defined
          (VarSet.union dropped cleared); }
  in
  let initial_state = {declared = ModedVarSet.empty; defined = ModedVarSet.empty} in
  let res = Analysis.forward_analysis initial_state seg merge update in
  let finish pc res =
    let annotation = annotations.(pc) in
    let instr = instructions.(pc) in
    match res with
    | None -> Dead
    | Some res ->
      let must_have_declared vars =
        let declared = ModedVarSet.untyped res.declared in
        if not (VarSet.subset vars declared)
        then raise (UndeclaredVariable (VarSet.diff vars declared, pc)) in
      must_have_declared (Instr.required_vars instr);
      begin match annotation with
        | None -> ()
        | Some (At_least xs | Exact xs) -> must_have_declared xs;
      end;
      let must_have_defined vars =
        let defined = ModedVarSet.untyped res.defined in
        if not (VarSet.subset vars defined)
        then raise (UninitializedVariable (VarSet.diff vars defined, pc)) in
      must_have_defined (Instr.used_vars instr);
      Scope res.declared
  in
  Array.mapi finish res

