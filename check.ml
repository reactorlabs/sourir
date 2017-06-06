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
exception BranchLabelReused of pc
exception DuplicateLabel of label
exception MissingReturn

exception FallthroughLabel of pc
exception EntryPointIsLabel

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
    let formals = List.map (fun (Param x) -> x) formals in
    let check seen var =
      if VarSet.mem var seen
      then raise (DuplicateParameter (name, var))
      else VarSet.add var seen
    in ignore (List.fold_left check VarSet.empty formals)
  in

  let check_version func (version:version) =
    let instrs = version.instrs in

    if func.name <> "main" then
      begin if Array.length instrs = 0 then raise MissingReturn;
      begin match[@warning "-4"] instrs.((Array.length instrs) - 1) with
      | Return _ | Stop _ | Goto _ | Branch _ -> ()
      | _ -> raise MissingReturn end
    end;

    let check_signature pc (func:afunction) args =
      if (List.length args <> List.length func.formals)
      then raise (InvalidNumArgs pc)
    in

    let preds = Analysis.predecessors instrs in
    let check_fun_ref instr =
      let rec check_value = function
        | Nil | Bool _ | Int _ | Array _ -> ()
        | Fun_ref x -> ignore (lookup_fun x)
      in
      let check_simple_expr = function
        | Var _ -> ()
        | Constant v -> check_value v
      in
      let check_expr = function
        | Simple e -> check_simple_expr e
        | Unop (_op, e) ->
          check_simple_expr e
        | Binop (_op, e1, e2) ->
          check_simple_expr e1;
          check_simple_expr e2
        | Array_index (_, i) ->
          check_simple_expr i
        | Array_length (e) ->
          check_simple_expr e in
      let check_arg = check_expr in
      let check_osr = function
        | Osr_var (_, e) -> check_expr e
      in
      match instr with
      | Call (_x, f, es) ->
        (check_expr f;
         List.iter check_arg es)
      | Decl_var (_, e)
      | Decl_array (_, Length e)
      | Assign (_, e)
      | Print e
      | Assert e
      | Stop e
      | Return e
      | Branch (e, _, _)
        -> check_expr e
      | Decl_array (_, List es) -> List.iter check_expr es
      | Drop _ | Read _
      | Goto _ | Label _ | Comment _ -> ()
      | Array_assign (_, i, e) ->
        check_expr i;
        check_expr e;
      | Osr {cond; map} ->
        List.iter check_expr cond;
        List.iter check_osr map
    in

    let seen = ref [] in

    (* Check correctness of calls and osrs *)
    let check_instr pc instr =
      match[@warning "-4"] instr with
      | Call (x, f, exs) ->
        (* if it's a static call check that the function exists and if the
         * actual arguments are compatible with the formals *)
        begin match[@warning "-4"] f with
        | (Simple (Constant (Fun_ref f))) ->
          let func' = lookup_fun f in
          check_signature pc func' exs
        | _ -> ()
        end;
        check_fun_ref instr
      | Osr {target = {func; version; pos=label}} ->
        (* check if the function exists and if the actual arguments
         * are compatible with the formals *)
        let func = lookup_fun func in
        let vers = lookup_version func version in
        let _ = Instr.resolve_osr vers.instrs label in
        check_fun_ref instr
      | Goto l ->
        let _ = Instr.resolve instrs (MergeLabel l) in
        check_fun_ref instr
      | Branch (e, l1, l2) ->
        let t1 = Instr.resolve instrs (BranchLabel l1) in
        if (preds.(t1) <> [pc]) then raise (BranchLabelReused t1);
        let t2 = Instr.resolve instrs (BranchLabel l2) in
        if (preds.(t2) <> [pc]) then raise (BranchLabelReused t2);
        if (t1 = t2) then raise (BranchLabelReused t1);
        check_fun_ref instr
      | Label (MergeLabel l| BranchLabel l) ->
        if List.mem l !seen then raise (DuplicateLabel l);
        seen := l :: !seen;
        (* Entry point cannot be a label because if it where a branch
         * target it would have two incoming control flows. *)
        if (pc = 0) then raise EntryPointIsLabel;
        (* Fallthrough is forbidden. Because again for branch targets
         * it would add a second source. To simplify resoning we forbid
         * it in general. *)
        begin match[@warning "-4"] instrs.(pc-1) with
        | Goto _ | Branch _ | Stop _ | Return _ -> ()
        | _ -> raise (FallthroughLabel pc)
        end;
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

