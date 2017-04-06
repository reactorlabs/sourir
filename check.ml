open Instr

exception MissingMain
exception DuplicateFunctionDeclaration of identifier
exception InvalidFunctionDeclaration of identifier
exception DuplicateVersion of identifier * label
exception EmptyFunction of identifier
exception DuplicateParameter of identifier * variable

exception ErrorAt of identifier * label * exn

(* Those should always come wrapped in an ErrorAt : *)
exception FunctionDoesNotExist of identifier
exception VersionDoesNotExist of identifier * label
exception InvalidNumArgs of pc
exception InvalidArgument of pc * expression
exception MissingReturn


module IdentifierSet = Set.Make(Identifier)

let well_formed prog =
  (* Check if main exists and expects no arguments *)
  let check_main main =
    if main.name <> "main" then raise MissingMain;
    if main.formals <> [] then raise (InvalidFunctionDeclaration "main");
  in
  check_main prog.main;

  let lookup_version func label =
    match List.filter (fun {label=l} -> label = l) func.body with
    | [] -> raise (VersionDoesNotExist (func.name, label))
    | [v] -> v
    | _ -> assert (false)
  in
  let lookup_fun name =
    match List.filter (fun {name = l} -> name = l) prog.functions with
    | [] -> raise (FunctionDoesNotExist name)
    | [f] -> f
    | _ -> assert (false)
  in

  let functions = prog.main :: prog.functions in

  (* Formals args shall not contain duplicate variables *)
  let check_formals name formals =
    let formals = List.map (fun f -> match f with
        | ParamConst x -> x | ParamMut x -> x) formals in
    List.iter (fun f ->
        if List.length (List.filter (fun f' -> f=f') formals) > 1 then
          raise (DuplicateParameter (name, f))) formals
  in

  let check_version func version =
    let instrs = version.instrs in

    if func.name <> "main" then
    begin if Array.length instrs = 0 then raise MissingReturn else
      begin match[@warning "-4"] instrs.((Array.length instrs) - 1) with
      | Return _ | Stop _ | Goto _ | Branch _ -> ()
      | _ -> raise MissingReturn end
    end;

    let scope = Scope.infer func version in

    (* Check correctness of calls and osrs *)
    let check_instr pc instr =
      match[@warning "-4"] instr with
      | Call (x, f, exs) ->
        (* check if the function exists and if the actual arguments
         * are compatible with the formals *)
        let func' = lookup_fun f in
        if (List.length exs <> List.length func'.formals)
        then raise (InvalidNumArgs pc);
        let check_arg (formal, actual) =
            match formal with
            | ParamConst _ -> ()
            | ParamMut x ->
              begin match[@warning "-4"] actual with
              | Simple (Var x) ->
                begin match scope.(pc) with
                | DeadScope -> ()
                | Scope scope ->
                  ignore (try ModedVarSet.find (Mut_var, x) scope with
                          | Not_found -> raise (InvalidArgument (pc, actual)))
                end
              | _ -> raise (InvalidArgument (pc, actual))
              end
        in
        List.iter check_arg (List.combine func'.formals exs)

      | Osr (e, f, v, l, osr) ->
        (* function and version mentioned in the osr need to exist *)
        let func = lookup_fun f in
        let vers = lookup_version func v in
        let _ = Instr.resolve vers.instrs l in
        ()
      | _ -> ()
    in
    Array.iteri check_instr instrs
  in

  let check_function func =
    if func.body = [] then raise (EmptyFunction func.name);
    check_formals func.name func.formals;
    List.iter (fun version ->
        let all = List.filter (fun {label=o} -> o=version.label) func.body in
        if List.length all > 1 then raise (DuplicateVersion (func.name, version.label));
        try check_version func version with
        | e -> raise (ErrorAt (func.name, version.label, e))
      ) func.body
  in

  List.iter (fun func ->
      let all = List.filter (fun {name=o} -> func.name=o) functions in
      if List.length all > 1 then raise (DuplicateFunctionDeclaration func.name);
      check_function func;) functions;
  ()


