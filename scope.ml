open Instr

(* TODO:
    - keep track of const/mut status
*)

exception UndeclaredVariable of VarSet.t * pc
exception UninitializedVariable of VarSet.t * pc
exception ExtraneousVariable of VarSet.t * pc
exception DuplicateVariable of VarSet.t * pc

type scope_info = ModedVarSet.t

module PcSet = Set.Make(Pc)
type inference_state = {
  sources : PcSet.t;
  info : scope_info;
}

type scope_annotation =
  | Exact of VarSet.t
  | At_least of VarSet.t

type inferred_scope =
  | Dead
  | Scope of ModedVarSet.t

type stream_annotation = scope_annotation option array
type annotated_program = (instruction_stream * stream_annotation) Instr.dict

let drop_annots : annotated_program -> program =
  List.map (fun (name, (instrs, annot)) -> (name, instrs))

exception IncompatibleScope of inference_state * inference_state * pc

let infer instructions : inferred_scope array =
  let open Analysis in

  let infer_scope instructions =
    let merge pc cur incom =
      if not (ModedVarSet.equal cur.info incom.info)
      then raise (IncompatibleScope (cur, incom, pc))
      else if PcSet.equal cur.sources incom.sources then None
      else Some { info = cur.info; sources = PcSet.union cur.sources incom.sources }
    in
    let update pc cur =
      let instr = instructions.(pc) in
      let added = Instr.declared_vars instr in
      let info = cur.info in
      let shadowed = ModedVarSet.inter info added in
      if not (ModedVarSet.is_empty shadowed) then
        raise (DuplicateVariable (ModedVarSet.untyped shadowed, pc));
      let updated = ModedVarSet.union info added in
      let dropped = Instr.dropped_vars instr in
      let final_info = ModedVarSet.diff_untyped updated dropped in
      { sources = PcSet.singleton pc; info = final_info; }
    in
    let initial_state = { sources = PcSet.empty; info = ModedVarSet.empty; } in
    let res = Analysis.forward_analysis initial_state instructions merge update in
    fun pc -> (res pc).info in

  let check_initialized instructions =
    let merge pc cur incom =
      let merged = ModedVarSet.inter cur incom in
      if ModedVarSet.equal cur merged then None else Some merged
    in
    let update pc cur =
      let instr = instructions.(pc) in
      let written = Instr.defined_vars instr in
      let updated = ModedVarSet.union cur written in
      let dropped, cleared = Instr.dropped_vars instr, Instr.cleared_vars instr in
      (* dropped variables must also be undefined, to preserve the property
         that only declared variables are defined. *)
      ModedVarSet.diff_untyped updated (VarSet.union dropped cleared)
    in
    let initial_state = ModedVarSet.empty in
    Analysis.forward_analysis initial_state instructions merge update in

  let inferred = infer_scope instructions in
  let initialized = check_initialized instructions in

  let resolve pc instr =
    match inferred pc, initialized pc with
    | exception Analysis.UnreachableCode _ -> Dead
    | declared, defined ->
      let defined' = ModedVarSet.untyped defined in
      let declared' = ModedVarSet.untyped declared in
      let used = Instr.used_vars instr in
      let required = Instr.required_vars instr in
      if not (VarSet.subset required declared')
      then raise (UndeclaredVariable (VarSet.diff required declared', pc));
      if not (VarSet.subset used defined')
      then raise (UninitializedVariable (VarSet.diff used defined', pc));
      Scope defined in

  Array.mapi resolve instructions

let check (scope : inferred_scope array) annotations =
  let check_at pc scope =
    match scope with
    | Dead -> ()
    | Scope scope ->
      begin match annotations.(pc) with
        | None -> ()
        | Some (At_least vars) ->
          let declared = ModedVarSet.untyped scope in
          if not (VarSet.subset vars declared)
          then raise (UndeclaredVariable (VarSet.diff vars declared, pc))
        | Some (Exact vars) ->
          let declared = ModedVarSet.untyped scope in
          if not (VarSet.subset vars declared)
          then raise (UndeclaredVariable (VarSet.diff vars declared, pc));
          if not (VarSet.subset declared vars)
          then raise (ExtraneousVariable (VarSet.diff declared vars, pc))
      end
  in
  Array.iteri check_at scope

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
    let print_diff diff =
      if not (ModedVarSet.is_empty diff) then
        Printf.bprintf buf
          "  - the %s declares %a and the %s does not\n"
          name1 print_vars diff name2 in
    print_diff diff;
  in
  Printf.bprintf buf
    "At instruction %d,\n\
     the scope coming from %a and\n\
     the scope coming from %a\n\
     are incompatible:\n"
    pc
    print_sources s1.sources
    print_sources s2.sources;
  print_only buf "former" (ModedVarSet.diff s1.info s2.info) "latter";
  print_only buf "latter" (ModedVarSet.diff s2.info s1.info) "former";
  Buffer.output_buffer outchan buf
