open Instr

(* TODO:
    - keep track of const/mut status
*)

exception UndeclaredVariable of VarSet.t * pc
exception ExtraneousVariable of VarSet.t * pc
exception DuplicateVariable of VarSet.t * pc

type scope_info = VarSet.t

module PcSet = Set.Make(Pc)
type inference_state = {
  sources : PcSet.t;
  info : scope_info;
}

exception IncompatibleScope of inference_state * inference_state * pc

let infer ({formals; instrs} : analysis_input) : inferred_scope array =
  let open Analysis in

  let infer_scope instructions =
    let merge pc cur incom =
      if not (VarSet.equal cur.info incom.info)
      then raise (IncompatibleScope (cur, incom, pc))
      else if PcSet.equal cur.sources incom.sources then None
      else Some { info = cur.info; sources = PcSet.union cur.sources incom.sources }
    in
    let update pc cur =
      let instr = instructions.(pc) in
      let added = Instr.declared_vars instr in
      let info = cur.info in
      let shadowed = VarSet.inter info added in
      if not (VarSet.is_empty shadowed) then
        raise (DuplicateVariable (shadowed, pc));
      let updated = VarSet.union info added in
      let dropped = Instr.dropped_vars instr in
      let final_info = VarSet.diff updated dropped in
      { sources = PcSet.singleton pc; info = final_info; }
    in
    let initial_state = { sources = PcSet.empty; info = formals; } in
    let res = Analysis.forward_analysis initial_state instrs merge update in
    fun pc -> (res pc).info in

  let inferred = infer_scope instrs in

  let resolve pc instr =
    match inferred pc with
    | exception Analysis.UnreachableCode _ -> DeadScope
    | declared ->
      let required = Instr.required_vars instr in
      if not (VarSet.subset required declared)
      then raise (UndeclaredVariable (VarSet.diff required declared, pc));
      Scope declared in

  Array.mapi resolve instrs

let check (scope : inferred_scope array) annotations =
  let check_at pc scope =
    match scope with
    | DeadScope -> ()
    | Scope scope ->
      begin match annotations.(pc) with
        | None -> ()
        | Some (AtLeastScope vars) ->
          let declared = scope in
          if not (VarSet.subset vars declared)
          then raise (UndeclaredVariable (VarSet.diff vars declared, pc))
        | Some (ExactScope vars) ->
          let declared = scope in
          if not (VarSet.subset vars declared)
          then raise (UndeclaredVariable (VarSet.diff vars declared, pc));
          if not (VarSet.subset declared vars)
          then raise (ExtraneousVariable (VarSet.diff declared vars, pc))
      end
  in
  Array.iteri check_at scope

exception ScopeExceptionAt of label * label * exn

let check_function (func : afunction) =
  List.iter (fun (version : version) ->
      let check () =
        let inferred = infer (Analysis.as_analysis_input func version) in
        match version.annotations with
        | None ->
          let annot = Array.map (fun _ -> None) version.instrs in
          check inferred annot
        | Some annot ->
          check inferred annot
      in
      try check () with
      | e -> raise (ScopeExceptionAt (func.name, version.label, e))
    ) func.body

let check_program (prog : program) =
  List.iter (fun func ->
      check_function func) (prog.main :: prog.functions)

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
    let print_var buf var =
      Printf.bprintf buf "var %s" var in
    let vars = VarSet.elements vars |> Array.of_list in
    Printf.bprintf buf "{";
    print_sep buf print_var vars ", " ", ";
    Printf.bprintf buf "}";
  in
  let print_only buf name1 diff name2 =
    let print_diff diff =
      if not (VarSet.is_empty diff) then
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
  print_only buf "former" (VarSet.diff s1.info s2.info) "latter";
  print_only buf "latter" (VarSet.diff s2.info s1.info) "former";
  Buffer.output_buffer outchan buf
