let () =
  match Sys.argv.(1) with
  | exception _ ->
    Printf.eprintf
      "You should provide a Sourir file to parse as command-line argument.\n\
       Example: %s examples/sum.sou\n%!"
      Sys.executable_name;
    exit 1
  | path ->
    let program =
      try Parse.parse_file path
      with Parse.Error error ->
        Parse.report_error error;
        exit 2
    in
    let quiet = Array.exists (fun arg -> arg = "--quiet") Sys.argv in
    let prune = Array.exists (fun arg -> arg = "--prune") Sys.argv in

    List.iter (fun (name, segment) ->
      match Scope.infer segment with
      | exception Scope.UndeclaredVariable (xs, pc) ->
        let l = pc+1 in
        begin match Instr.VarSet.elements xs with
          | [x] -> Printf.eprintf "%d : Error: Variable %s is not declared.\n%!" l x
          | xs -> Printf.eprintf "%d : Error: Variables {%s} are not declared.\n%!"
                    l (String.concat ", " xs)
        end;
        exit 1
      | exception Scope.UninitializedVariable (xs, pc) ->
        let l = pc+1 in
        begin match Instr.VarSet.elements xs with
          | [x] -> Printf.eprintf "%d : Error: Variable %s might be uninitialized.\n%!" l x
          | xs -> Printf.eprintf "%d : Error: Variables {%s} might be uninitialized.\n%!"
                    l (String.concat ", " xs)
        end;
        exit 1
      | exception Scope.ExtraneousVariable (xs, pc) ->
        let l = pc+1 in
        begin match Instr.VarSet.elements xs with
          | [x] -> Printf.eprintf "%d : Error: Variable %s is unexpected in scope.\n%!" l x
          | xs -> Printf.eprintf "%d : Error: Variables {%s} are unexpected in scope.\n%!"
                    l (String.concat ", " xs)
        end;
        exit 1
      | exception Scope.DuplicateVariable (xs, pc) ->
        let l = pc+1 in
        begin match Instr.VarSet.elements xs with
          | [x] -> Printf.eprintf "%d : Error: Variable %s is declared more than once.\n%!" l x
          | xs -> Printf.eprintf "%d : Error: Variables {%s} are declared more than once.\n%!"
                    l (String.concat ", " xs)
        end;
        exit 1
      | exception Scope.IncompatibleScope (scope1, scope2, pc) ->
        Disasm.pretty_print_segment stderr (name, segment);
        Scope.explain_incompatible_scope stderr scope1 scope2 pc;
        flush stderr;
        exit 1

      | scopes -> ()) program;

      let program = if prune
        then
          let opt = Transform.branch_prune program in
          if not quiet then Printf.printf "%s" (Disasm.disassemble opt);
          opt
        else program
      in
      ignore (Eval.run_interactive IO.stdin_input program)
