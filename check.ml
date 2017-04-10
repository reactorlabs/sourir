open Instr

(* These are exceptions at the scope of the program *)
exception MissingMain
exception InvalidMain
exception DuplicateFunctionDeclaration of identifier
exception DuplicateVersion of identifier * label
exception EmptyFunction of identifier
exception DuplicateParameter of identifier * variable

(* The following are exceptions at the scope of a particular
 * function body. To indicate the position where they occur
 * they will be wrapped in a ErrorAt exception. *)
exception ErrorAt of identifier * label * exn

exception FunctionDoesNotExist of identifier
exception VersionDoesNotExist of identifier * label
exception InvalidNumArgs of pc
exception InvalidArgument of pc * argument
exception MissingReturn


module IdentifierSet = Set.Make(Identifier)

let well_formed prog =
  (* Check if main exists and expects no arguments *)
  let check_main main =
    if main.name <> "main" then raise MissingMain;
    if main.formals <> [] then raise InvalidMain;
  in
  check_main prog.main;

  let lookup_version func label =
    try List.find (fun {label=l} -> label = l) func.body with
    | Not_found -> raise (VersionDoesNotExist (func.name, label))
  in
  let lookup_fun name =
    if name = "main" then prog.main else
    try List.find (fun {name = l} -> name = l) prog.functions with
    | Not_found -> raise (FunctionDoesNotExist name)
  in

  let functions = prog.main :: prog.functions in

  (* Formals args shall not contain duplicate variables *)
  let check_formals name formals =
    let formals = List.map (fun f -> match f with
        | Const_val_param x -> x | Mut_ref_param x -> x) formals in
    let check seen var =
      if VarSet.mem var seen
      then raise (DuplicateParameter (name, var))
      else VarSet.add var seen
    in ignore (List.fold_left check VarSet.empty formals)
  in

  let check_version func version =
    let instrs = version.instrs in

    if func.name <> "main" then
      begin if Array.length instrs = 0 then raise MissingReturn;
      begin match[@warning "-4"] instrs.((Array.length instrs) - 1) with
      | Return _ | Stop _ | Goto _ | Branch _ -> ()
      | _ -> raise MissingReturn end
    end;

    let scope = Scope.infer func version in

    let check_static_arg pc actual =
      match actual with
      | Arg_by_val _ -> ()
      | Arg_by_ref x ->
        begin match scope.(pc) with
        | DeadScope -> ()
        | Scope scope ->
          ignore (try ModedVarSet.find (Mut_var, x) scope with
                  | Not_found -> raise (InvalidArgument (pc, actual))
                  | Incomparable -> raise (InvalidArgument (pc, actual)))
        end in

    let check_signature pc func args =
      if (List.length args <> List.length func.formals)
      then raise (InvalidNumArgs pc);
      let check_arg (formal, actual) =
        match[@warning "-4"] formal, actual with
        | Const_val_param _, Arg_by_val _
        | Mut_ref_param _, Arg_by_ref _ -> ()
        | _ -> raise (InvalidArgument (pc, actual)) in
      List.iter check_arg (List.combine func.formals args) in

    let check_fun_ref instr =
      let check_simple_expr = function
        | Var _
        | Lit (Nil | Bool _ | Int _) -> ()
        | Lit (Fun_ref x) -> ignore (lookup_fun x) in
      let check_expr = function
        | Simple e -> check_simple_expr e
        | Op (_op, xs) ->
          List.iter check_simple_expr xs in
      let check_arg = function
        | Arg_by_val e -> check_expr e
        | Arg_by_ref x -> () in
      let check_osr = function
        | Osr_const (_, e) -> check_expr e
        | Osr_mut _ | Osr_mut_undef _ -> () in
      match instr with
      | Call (_x, f, es) ->
        (check_expr f;
         List.iter check_arg es)
      | Decl_const (_, e)
      | Decl_mut (_, Some e)
      | Assign (_, e)
      | Branch (e, _, _)
      | Print e
      | Stop e
      | Return e ->
        check_expr e
      | Decl_mut (_, None)
      | Drop _ | Clear _ | Read _
      | Label _ | Goto _ | Comment _ -> ()
      | Osr (e, _, _, _, osr) ->
        check_expr e;
        List.iter check_osr osr
    in

    (* Check correctness of calls and osrs *)
    let check_instr pc instr =
      match[@warning "-4"] instr with
      | Call (x, f, exs) ->
        (* Check call-by-name args are mut *)
        List.iter (check_static_arg pc) exs;
        (* if it's a static call check that the function exists and if the
         * actual arguments are compatible with the formals *)
        begin match[@warning "-4"] f with
        | (Simple (Lit (Fun_ref f))) ->
          let func' = lookup_fun f in
          check_signature pc func' exs
        | _ -> ()
        end;
        check_fun_ref instr
      | Osr (e, f, v, l, osr) ->
        (* function and version mentioned in the osr need to exist *)
        let func = lookup_fun f in
        let vers = lookup_version func v in
        let _ = Instr.resolve vers.instrs l in
        check_fun_ref instr
      | _ -> check_fun_ref instr
    in
    Array.iteri check_instr instrs
  in

  let check_function func =
    if func.body = [] then raise (EmptyFunction func.name);
    check_formals func.name func.formals;
    let check seen {label} =
      if VarSet.mem label seen
      then raise (DuplicateVersion (func.name, label))
      else VarSet.add label seen
    in ignore (List.fold_left check VarSet.empty func.body);
    List.iter (fun version ->
        try check_version func version with
        | e -> raise (ErrorAt (func.name, version.label, e))
      ) func.body
  in

  List.iter (fun func ->
      let all = List.filter (fun {name} -> name=func.name) functions in
      if List.length all > 1 then raise (DuplicateFunctionDeclaration func.name);
      check_function func;) functions;
  ()


