open Instr

let run = ref true
let quiet = ref false
let autofix = ref false
let opts = ref []
let path = ref ""
let ott = ref false
let num_opts = ref 1

let () =
  let cmd_args = [
    ("--run", Arg.Set run, "run the program (default)");
    ("--no-run", Arg.Clear run, "do not run the program, just show the optimized source code");
    ("--quiet", Arg.Set quiet, "quiet");
    ("--autofix", Arg.Set autofix, "automatically normalize graph");
    ("--opt", Arg.String (fun s -> opts := String.split_on_char ',' s), "Enable optimizations");
    ("--num", Arg.String (fun s -> num_opts := int_of_string s), "Number of optimization runs");
    ("--ott", Arg.Set ott, "Output ott rendering");
  ] in
  Arg.parse cmd_args (fun s ->
      if !path <> "" then raise (Arg.Bad ("Invalid argument "^s));
      path := s) "options";

  if !path = "" then (
    Printf.eprintf
      "You should provide a Sourir file to parse as command-line argument.\n\
       Example: %s examples/sum.sou\n%!"
      Sys.executable_name;
    exit 1);

  let program =
    try Parse.program_of_file !path
    with Parse.Error error ->
      Parse.report_error error;
      exit 2
  in

  let program =
    if !autofix
    then Transform.try_opt Transform.normalize_graph program
    else program in

  opts := if !opts = ["all"] then Transform.all_opts else !opts;

  let check_prog program =
    begin try Check.well_formed program with
    | Check.MissingMain ->
      Printf.eprintf "Program is missing an explicit or implicit main function\n";
      exit 1
    | Check.InvalidMain ->
      Printf.eprintf "Main function cannot have arguments\n";
      exit 1
    | Check.DuplicateFunctionDeclaration f ->
      Printf.eprintf "Duplicate function declaration %s\n" f;
      exit 1
    | Check.DuplicateVersion (f, v) ->
      Printf.eprintf "Version %s in function %s is defined twice\n" v f;
      exit 1
    | Check.EmptyFunction f ->
      Printf.eprintf "Function %s has no body\n" f;
      exit 1
    | Check.DuplicateParameter (f, x) ->
      Printf.eprintf "Function %s : parameter %s is given twice\n" f x;
      exit 1
    | Check.ErrorAt (f, v, e) ->
      Printf.eprintf "Error in function %s version %s: " f v;
      begin match[@warning "-4"] e with
      | Check.MissingReturn ->
        Printf.eprintf "missing return statement\n"
      | Check.FunctionDoesNotExist f' ->
        Printf.eprintf "called function %s does not exist\n" f'
      | Check.VersionDoesNotExist (f', v') ->
        Printf.eprintf "bailout target %s %s does not exist\n" f' v'
      | Check.InvalidNumArgs pc ->
        Printf.eprintf "at line %d: invalid number of arguments\n" (pc+1)
      | Check.InvalidArgument (pc, expression) ->
        Printf.eprintf "at line %d: invalid argument\n" (pc+1)
      | Instr.Unbound_label (MergeLabel l) ->
        Printf.eprintf "label %s does not exist\n" l
      | Instr.Unbound_label (BranchLabel l) ->
        Printf.eprintf "label $%s does not exist\n" l
      | Instr.Unbound_bailout_label l ->
        Printf.eprintf "bailout target %s does not exist\n" l
      | Check.BranchLabelReused pc ->
        Printf.eprintf "label at line %d is used more than once\n" (pc+1)
      | Check.FallthroughLabel pc ->
        Printf.eprintf "fallthrough label at line %d is not allowed\n" (pc+1)
      | Check.EntryPointIsLabel ->
        Printf.eprintf "the first instruction cannot be a label\n"
      | Check.DuplicateLabel l ->
        Printf.eprintf "label %s used multiple times\n" l
      | _ -> raise e
      end;
      exit 1
    end
  in
  check_prog program;

  begin try Scope.check_program program with
  | Scope.ScopeExceptionAt _ as exn ->
    Printf.eprintf "Scope error in the source program:\n";
    Scope.report_error program exn
  end;

  let optimize program =
    let optimizations = Transform.optimize !opts !num_opts in
    Transform.(try_opt optimizations program)
  in

  let program = try optimize program with
    | Transform.UnknownOptimization opt ->
      Printf.eprintf "Unknown optimization %s.\nValid optimizers are %s\n"
        opt (String.concat ", " (Transform.all_opts @ Transform.manual_opts));
      exit 1
  in

  if !ott then begin
    Ott.disassemble_o stdout program;
    exit 0
  end;

  if not !quiet then begin
    Printf.printf "After optimizations\n";
    Disasm.disassemble_o stdout program
  end;

  check_prog program;
  begin try Scope.check_program program with
  | Scope.ScopeExceptionAt _ as exn ->
    Printf.eprintf "Scope error in the optimized program (%s):\n"
      (String.concat ", " !opts);
    Scope.report_error program exn
  end;

  if not !run then ()
  else begin
    let conf = Eval.run_interactive IO.stdin_input program in
    let open Eval in
    match conf.status with
    | Running -> assert(false)
    | Result (Int n) ->
      exit n
    | Result (Bool b) ->
      exit (if b then 1 else 0)
    | Result (String _ | Fun_ref _ | Array _ | Nil) ->
      exit 0
  end
