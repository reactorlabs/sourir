let () =
  match Sys.argv.(1) with
  | exception _ ->
    Printf.eprintf
      "You should provide a Sourir file to parse as command-line argument.\n\
       Example: %s test.sou\n%!"
      Sys.executable_name;
    exit 1
  | path ->
    let annotated_program = Parse.parse_file path in
    begin match Scope.infer annotated_program with
      | exception Scope.UndefinedVariable xs ->
        begin match Scope.VarSet.elements xs with
          | [x] -> Printf.eprintf "Error: Variable %s undefined.\n%!" x
          | xs -> Printf.eprintf "Error: Variables {%s} undefined.\n%!"
                    (String.concat ", " xs)
        end;
        exit 1
      | _scopes ->
        let program = fst annotated_program in
        ignore (Eval.run_interactive program)
    end
