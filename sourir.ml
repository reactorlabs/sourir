let () =
  match Sys.argv.(1) with
  | exception _ ->
    Printf.eprintf
      "You should provide a Sourir file to parse as command-line argument.\n\
       Example: %s examples/sum.sou\n%!"
      Sys.executable_name;
    exit 1
  | path ->
    let annotated_program =
      try Parse.parse_file path
      with Parse.Error error ->
        Parse.report_error error;
        exit 2
    in
    begin match Scope.infer annotated_program with
      | exception Scope.UndeclaredVariable xs ->
        begin match Instr.VarSet.elements xs with
          | [x] -> Printf.eprintf "Error: Variable %s is not declared.\n%!" x
          | xs -> Printf.eprintf "Error: Variables {%s} are not declared.\n%!"
                    (String.concat ", " xs)
        end;
        exit 1
      | exception Scope.UninitializedVariable xs ->
        begin match Instr.VarSet.elements xs with
          | [x] -> Printf.eprintf "Error: Variable %s might be uninitialized.\n%!" x
          | xs -> Printf.eprintf "Error: Variables {%s} might be uninitialized.\n%!"
                    (String.concat ", " xs)
        end;
        exit 1
      | exception Scope.DuplicateVariable xs ->
        begin match Instr.VarSet.elements xs with
          | [x] -> Printf.eprintf "Error: Variable %s is declared more than once.\n%!" x
          | xs -> Printf.eprintf "Error: Variables {%s} are declared more than once.\n%!"
                    (String.concat ", " xs)
        end;
        exit 1
      | scopes ->
        let program = fst annotated_program in
        let program = if ((Array.length Sys.argv > 2) && (Sys.argv.(2) = "--prune"))
          then
            let opt = Transform.branch_prune (program, scopes) in
            let () = Printf.printf "%s" (Disasm.disassemble opt) in
            opt
          else program
        in
        ignore (Eval.run_interactive IO.stdin_input program)
    end
