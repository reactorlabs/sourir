open Instr
open Types

(* TODO:
    - keep track of const/mut status
*)

exception UndeclaredVariable of VarSet.t * pc
exception ExtraneousVariable of VarSet.t * pc
exception DuplicateVariable of VarSet.t * pc

module Declaration = struct
  type t = string * pc
  let compare a b =
    if fst a = fst b then
      Pervasives.compare (snd a) (snd b)
    else
      String.compare (fst a) (fst b)
end
module DeclSet = Set.Make(Declaration)
let decl_as_var_set set =
  VarSet.of_list (fst (List.split (DeclSet.elements set)))

type scope_info = DeclSet.t

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
      if not (DeclSet.equal cur.info incom.info)
      then raise (IncompatibleScope (cur, incom, pc))
      else if PcSet.equal cur.sources incom.sources then None
      else Some { info = cur.info; sources = PcSet.union cur.sources incom.sources }
    in
    let update pc cur =
      let instr = instructions.(pc) in
      let declared = Instr.declared_vars instr in
      let declared' = VarSet.elements declared in
      let declared' = List.map (fun v -> (v, pc)) declared' in
      let declared' = DeclSet.of_list declared' in
      let info = cur.info in
      let shadowed = VarSet.inter (decl_as_var_set info) declared in
      if not (VarSet.is_empty shadowed) then
        raise (DuplicateVariable (shadowed, pc));
      let updated = DeclSet.union info declared' in
      let dropped = VarSet.elements (Instr.dropped_vars instr) in
      let remove set el = DeclSet.filter (fun (v, _) -> v <> el) set in
      let final_info = List.fold_left remove updated dropped in
      { sources = PcSet.singleton pc; info = final_info; }
    in
    let initial = List.map (fun var -> (var, -1)) (VarSet.elements formals) in
    let initial_state = { sources = PcSet.empty; info = DeclSet.of_list initial; } in
    let res = Analysis.forward_analysis initial_state instrs merge update in
    fun pc -> (res pc).info in

  let inferred = infer_scope instrs in

  let resolve pc instr =
    match inferred pc with
    | exception Analysis.UnreachableCode _ -> DeadScope
    | declared ->
      let declared = decl_as_var_set declared in
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
      Printf.bprintf buf "var %s(%d)" (fst var) (snd var) in
    let vars = DeclSet.elements vars |> Array.of_list in
    Printf.bprintf buf "{";
    print_sep buf print_var vars ", " ", ";
    Printf.bprintf buf "}";
  in
  let print_only buf name1 diff name2 =
    let print_diff diff =
      if not (DeclSet.is_empty diff) then
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
  print_only buf "former" (DeclSet.diff s1.info s2.info) "latter";
  print_only buf "latter" (DeclSet.diff s2.info s1.info) "former";
  Buffer.output_buffer outchan buf

let report_error program = function
  | ScopeExceptionAt (f, v, e) as exn ->
    begin
      Printf.eprintf "Error in function %s version %s " f v;
      begin match e with
      | UndeclaredVariable (xs, pc) ->
        let l = pc+1 in
        begin match VarSet.elements xs with
          | [x] -> Printf.eprintf
                     "line %d: Variable %s is not declared.\n%!"
                     l x
          | xs -> Printf.eprintf
                    "line %d: Variables {%s} are not declared.\n%!"
                    l (String.concat ", " xs)
        end;
      | ExtraneousVariable (xs, pc) ->
        let l = pc+1 in
        let func = lookup_fun program f in
        let version = get_version func v in
        let annot = match version.annotations with | Some a -> a | None -> assert(false) in
        let annot_vars = match annot.(pc) with
          | None | Some (AtLeastScope _) ->
            (* we know from the exception-raising code that this cannot happen *)
            assert (false)
          | Some (ExactScope vars) ->
            VarSet.elements vars |>
            String.concat ", " |> Printf.sprintf " {%s}" in
        begin match VarSet.elements xs with
          | [x] -> Printf.eprintf
                     "line %d: Variable %s is present in scope but missing \
                     from the scope annotation%s.\n%!"
                     l x annot_vars
          | xs -> Printf.eprintf
                    "line %d: Variables {%s} are present in scope \
                     but missing from the scope annotation%s.\n%!"
                    l (String.concat ", " xs) annot_vars
        end;
      | DuplicateVariable (xs, pc) ->
        let l = pc+1 in
        begin match VarSet.elements xs with
          | [x] -> Printf.eprintf
                     "line %d: Variable %s is declared more than once.\n%!"
                     l x
          | xs -> Printf.eprintf
                    "line %d: Variables {%s} are declared more than once.\n%!"
                    l (String.concat ", " xs)
        end;
      | IncompatibleScope (scope1, scope2, pc) ->
        let func = lookup_fun program f in
        let version = get_version func v in
        let instrs = version.instrs in
        Disasm.pretty_print_version stderr (v, instrs);
        explain_incompatible_scope stderr scope1 scope2 pc;
        flush stderr;
      | _ -> raise exn
      end;
      exit 1
    end
  | exn -> raise exn
