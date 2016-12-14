open Instr

let disassemble (prog : (Scope.scope_annotation option * Instr.instruction) array) =
  let dump_instr buf (instr_annot : (Scope.scope_annotation option * Instr.instruction)) =
    let pr = Printf.bprintf in
    let dump_expr exp =
      match exp with
      | Var v             -> pr buf "%s" v
      | Lit lit           -> pr buf "%s" (string_of_litteral lit)
      | Op (Plus, [a; b]) -> pr buf "(%s + %s)" a b
      | Op (Eq,   [a; b]) -> pr buf "(%s == %s)" a b
      | Op (_, _)         -> assert(false)
    in
    match instr_annot with
    | (annot, instr) ->
        let str_from_vars vars = String.concat ", " (Scope.VarSet.elements vars) in
        begin match annot with
        | Some (Scope.Exact e)    -> pr buf "{%s} "      (str_from_vars e)
        | Some (Scope.At_least e) -> pr buf "{%s, ...} " (str_from_vars e)
        | None -> ()
        end;
        begin match instr with
        | Decl_const (var, exp)           -> pr buf " const %s = " var; dump_expr exp
        | Decl_mut (var, exp)             -> pr buf " mut %s = " var; dump_expr exp
        | Assign (var, exp)               -> pr buf " %s <- " var; dump_expr exp
        | Branch (exp, l1, l2)            -> pr buf " branch "; dump_expr exp; pr buf " %s %s" l1 l2
        | Label label                     -> pr buf "%s:" label
        | Goto label                      -> pr buf " goto %s" label
        | Read var                        -> pr buf " read %s" var
        | Print exp                       -> pr buf " print "; dump_expr exp
        | Invalidate (exp, l, vars)       -> pr buf " invalidate "; dump_expr exp;
                                             pr buf " %s [%s]" l (String.concat ", " vars)
        | Stop                            -> pr buf " stop"
        | Comment str                     -> pr buf " #%s" str
        end;
        pr buf "\n"
  in
  let b = Buffer.create 1024 in
  Array.iter (dump_instr b) prog;
  Buffer.contents b
