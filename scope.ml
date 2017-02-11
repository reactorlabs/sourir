open Instr

(* TODO:
    - keep track of const/mut status
*)

exception UndeclaredVariable of VarSet.t * pc
exception UninitializedVariable of VarSet.t * pc
exception ExtraneousVariable of VarSet.t * pc
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

module PcSet = Set.Make(Pc)
type inference_state = {
  sources : PcSet.t;
  info : scope_info;
}

exception IncompatibleScope of inference_state * inference_state * pc

(* Internally we keep track of the declared and defined variables.
 * The output scopes and the annotations contain only the declarations. But
 * internally infer asserts that undefined variables are never used and
 * declarations do not shadow a previous one
 *)
let infer (seg : segment) : inferred_scope array =
  let instructions = fst seg in
  let annotations = snd seg in
  let open Analysis in
  let merge pc cur incom =
    if not (ScopeInfo.equal cur.info incom.info)
    then raise (IncompatibleScope (cur, incom, pc))
    else if PcSet.equal cur.sources incom.sources then None
    else Some { info = cur.info; sources = PcSet.union cur.sources incom.sources }
  in
  let update pc cur =
    let annot = annotations.(pc) in
    let instr = instructions.(pc) in
    let added = {
      declared = Instr.declared_vars instr;
      defined = Instr.defined_vars instr;
    } in
    let shadowed = ModedVarSet.inter cur.info.declared added.declared in
    if not (ModedVarSet.is_empty shadowed) then
      raise (DuplicateVariable (ModedVarSet.untyped shadowed, pc));
    let info = cur.info in
    let info =
      { info with
        declared = begin match annot with
          | None | Some (At_least _) -> info.declared
          | Some (Exact constraints) ->
            ModedVarSet.inter_untyped info.declared constraints
        end
      } in
    let updated = ScopeInfo.union info added in
    let dropped, cleared = Instr.dropped_vars instr, Instr.cleared_vars instr in
    (* dropped variables must also be undefined, to preserve the property
       that only declared variables are defined. *)
    let final_info = {
      declared = ModedVarSet.diff_untyped updated.declared dropped;
      defined = ModedVarSet.diff_untyped updated.defined
          (VarSet.union dropped cleared);
    } in
    { sources = PcSet.singleton pc; info = final_info; }
  in
  let initial_state = {
    sources = PcSet.empty;
    info = {declared = ModedVarSet.empty; defined = ModedVarSet.empty};
  } in
  let res = Analysis.forward_analysis initial_state seg merge update in
  let finish pc res =
    let annotation = annotations.(pc) in
    let instr = instructions.(pc) in
    match res with
    | None -> Dead
    | Some { info = res; _ } ->
      let must_have_declared vars =
        let declared = ModedVarSet.untyped res.declared in
        if not (VarSet.subset vars declared)
        then raise (UndeclaredVariable (VarSet.diff vars declared, pc)) in
      let must_not_have_extra vars =
        let declared = ModedVarSet.untyped res.declared in
        if not (VarSet.subset declared vars)
        then raise (ExtraneousVariable (VarSet.diff declared vars, pc)) in
      must_have_declared (Instr.required_vars instr);
      begin match annotation with
        | None -> ()
        | Some (At_least vars) ->
          must_have_declared vars
        | Some (Exact vars) ->
          must_have_declared vars;
          must_not_have_extra vars;
      end;
      let must_have_defined vars =
        let defined = ModedVarSet.untyped res.defined in
        if not (VarSet.subset vars defined)
        then raise (UninitializedVariable (VarSet.diff vars defined, pc)) in
      must_have_defined (Instr.used_vars instr);
      Scope res.declared
  in
  Array.mapi finish res


let explain_incompatible_scope outchan s1 s2 pc =
  let buf = Buffer.create 100 in
  let print_sep buf print_elem elems sep last_sep =
    let len = Array.length elems in
    for i = 0 to len - 1 do
      print_elem buf elems.(i);
        if i = len - 1 then ()
        else if i = len - 1 then
          Printf.bprintf buf last_sep
        else
          Printf.bprintf buf sep
    done;
  in
  let print_sources buf sources =
    match PcSet.elements sources with
    | [] -> invalid_arg "explain_incompatible_scope: expect non-empty sources"
    | [pc] -> Printf.bprintf buf "instruction %d" pc
    | sources ->
      let sources = Array.of_list sources in
      Printf.bprintf buf "instructions ";
      print_sep buf (fun buf -> Printf.bprintf buf "%d") sources ", " " and "
  in
  let print_vars buf vars =
    let print_var buf (mode, var) =
      Printf.bprintf buf "%s %s"
        (match mode with Const_var -> "const" | Mut_var -> "mut") var in
    let vars = ModedVarSet.elements vars |> Array.of_list in
    Printf.bprintf buf "{";
    print_sep buf print_var vars ", " ", ";
    Printf.bprintf buf "}";
  in
  let print_only buf name1 diff name2 =
    let print_diff verb diff =
      if not (ModedVarSet.is_empty diff) then
        Printf.bprintf buf
          "  - the %s %s %a and the %s does not\n"
          name1 verb print_vars diff name2 in
    print_diff "declares" diff.declared;
    print_diff "defines"  (ModedVarSet.diff diff.defined diff.declared);
  in
  Printf.bprintf buf
    "At instruction %d,\n\
     the scope coming from %a and\n\
     the scope coming from %a\n\
     are incompatible:\n"
    pc
    print_sources s1.sources
    print_sources s2.sources;
  print_only buf "former" (ScopeInfo.diff s1.info s2.info) "latter";
  print_only buf "latter" (ScopeInfo.diff s2.info s1.info) "former";
  Buffer.output_buffer outchan buf
