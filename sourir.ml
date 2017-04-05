open Instr

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
    let quiet = Array.mem "--quiet" Sys.argv in
    let prune = Array.mem "--prune" Sys.argv in
    let codemotion = Array.mem "--cm" Sys.argv in
    let constprop = Array.mem "--prop" Sys.argv in
    let lifetime = Array.mem "--lifetime" Sys.argv in

    begin try Scope.check_program program with
    | Scope.ScopeExceptionAt (f, v, e) ->
      begin
        Printf.eprintf "Error in function %s version %s " f v;
        begin match e with
        | Scope.UndeclaredVariable (xs, pc) ->
          let l = pc+1 in
          begin match VarSet.elements xs with
            | [x] -> Printf.eprintf
                       "line %d: Variable %s is not declared.\n%!"
                       l x
            | xs -> Printf.eprintf
                      "line %d: Variables {%s} are not declared.\n%!"
                      l (String.concat ", " xs)
          end;
        | Scope.UninitializedVariable (xs, pc) ->
          let l = pc+1 in
          begin match VarSet.elements xs with
            | [x] -> Printf.eprintf
                       "line %d: Variable %s might be uninitialized.\n%!"
                       l x
            | xs -> Printf.eprintf
                      "line %d: Variables {%s} might be uninitialized.\n%!"
                      l (String.concat ", " xs)
          end;
        | Scope.ExtraneousVariable (xs, pc) ->
          let l = pc+1 in
          let func = lookup_fun program f in
          let annot = List.assoc v func.annotations in
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
        | Scope.DuplicateVariable (xs, pc) ->
          let l = pc+1 in
          begin match VarSet.elements xs with
            | [x] -> Printf.eprintf
                       "line %d: Variable %s is declared more than once.\n%!"
                       l x
            | xs -> Printf.eprintf
                      "line %d: Variables {%s} are declared more than once.\n%!"
                      l (String.concat ", " xs)
          end;
        | Scope.IncompatibleScope (scope1, scope2, pc) ->
          let func = lookup_fun program f in
          let instrs = List.assoc v func.body in
          Disasm.pretty_print_version stderr (v, instrs);
          Scope.explain_incompatible_scope stderr scope1 scope2 pc;
          flush stderr;
        | _ -> assert(false) end;
        exit 1
      end
    end;

    let program = if prune
      then
        let opt = { program with main = Transform.branch_prune program.main } in
        if not quiet then Printf.printf "\n** After speculative branch pruning:\n%s" (Disasm.disassemble_s opt);
        opt
      else program
    in

    let program = if codemotion
      then
        let opt = { program with main = Transform.hoist_assignment program.main } in
        if not quiet then Printf.printf "\n** After trying to hoist one assignment:\n%s" (Disasm.disassemble_s opt);
        opt
      else program
    in

    let program = if constprop
      then
        let opt = { program with main = Constantfold.const_prop program.main } in
        if not quiet then Printf.printf "\n** After constant propagation:\n%s" (Disasm.disassemble_s opt);
        opt
      else program
    in

    let program = if lifetime
      then
        let opt = { program with main = Transform.minimize_lifetimes program.main } in
        if not quiet then Printf.printf "\n** After minimizing lifetimes:\n%s" (Disasm.disassemble_s opt);
        opt
      else program
    in

    Scope.check_program program;

    let conf = Eval.run_interactive IO.stdin_input program in
    let open Eval in
    match conf.status with
    | Running -> assert(false)
    | Stopped None
      -> exit 0
    | Stopped (Some (Lit (Int n))) ->
      exit n
    | Stopped (Some (Lit (Bool b))) ->
      exit (if b then 1 else 0)
    | Stopped (Some (Lit Nil)) ->
      exit 0

