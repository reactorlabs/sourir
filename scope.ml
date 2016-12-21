open Instr

(* TODO:
    - keep track of const/mut status
*)

exception UndeclaredVariable of VarSet.t
exception UninitializedVariable of VarSet.t
exception DuplicateVariable of VarSet.t

type scope_info = { declared : VarSet.t; defined : VarSet.t }
module ScopeInfo = struct
  type t = scope_info
  let inter a b = {declared = VarSet.inter a.declared b.declared;
                   defined = VarSet.inter a.defined b.defined}
  let union a b = {declared = VarSet.union a.declared b.declared;
                   defined = VarSet.union a.defined b.defined}
  let equal a b = VarSet.equal a.declared b.declared &&
                  VarSet.equal a.defined b.defined
end

(* Internally we keep track of the declared and defined variables.
 * The output scopes and the annotations contain only the declarations. But
 * internally infer asserts that undefined variables are never used and
 * declarations do not shadow a previous one
 *)
let infer (program : annotated_program) : inferred_scope array =
  let instructions = fst program in
  let annotations = snd program in
  let open Analysis in
  let merge cur incom =
    let merged = ScopeInfo.inter cur incom in
    if ScopeInfo.equal cur merged then None else Some merged in
  let update pc cur =
    let annot = annotations.(pc) in
    let instr = instructions.(pc) in
    let update = { declared = Instr.declared_vars instr;
                   defined = Instr.defined_vars instr } in
    let shadowed = VarSet.inter cur.declared update.declared in
    if not (VarSet.is_empty shadowed) then raise (DuplicateVariable shadowed)
    else
      let cur =
        { cur with
          declared = begin match annot with
            | None | Some (At_least _) -> cur.declared
            | Some (Exact constraints) ->
              VarSet.inter cur.declared constraints
          end
        } in
      ScopeInfo.union cur update in
  let initial_state = {declared = VarSet.empty; defined = VarSet.empty} in
  let res = Analysis.forward_analysis initial_state instructions merge update in
  let finish pc res =
    let annotation = annotations.(pc) in
    let instr = instructions.(pc) in
    match res with
    | None -> Dead
    | Some res ->
      let must_have_declared vars =
        if not (VarSet.subset vars res.declared)
        then raise (UndeclaredVariable (VarSet.diff vars res.declared)) in
      must_have_declared (Instr.required_vars instr);
      begin match annotation with
        | None -> ()
        | Some (At_least xs | Exact xs) -> must_have_declared xs;
      end;
      let must_have_defined vars =
        if not (VarSet.subset vars res.defined)
        then raise (UninitializedVariable (VarSet.diff vars res.defined)) in
      must_have_defined (Instr.used_vars instr);
      Scope res.declared
  in
  Array.mapi finish res

