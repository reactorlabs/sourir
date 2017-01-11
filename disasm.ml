open Instr

let disassemble_annotated (prog : annotated_program) =
  let dump_instr buf instr annot =
    let pr = Printf.bprintf in
    let simple buf = function
      | Var v             -> pr buf "%s" v
      | Lit lit           -> pr buf "%s" (string_of_litteral lit)
    in
    let dump_expr exp =
      match exp with
      | Simple e          -> simple buf e
      | Op (Plus, [a; b]) -> pr buf "(%a + %a)" simple a simple b
      | Op (Neq,  [a; b]) -> pr buf "(%a != %a)" simple a simple b
      | Op (Eq,   [a; b]) -> pr buf "(%a == %a)" simple a simple b
      | Op ((Plus | Neq | Eq), _)         -> assert(false)
    in
    let str_from_vars vars = String.concat ", " (Instr.VarSet.elements vars) in
    begin match annot with
    | Some (Exact e)    -> pr buf "{%s} "      (str_from_vars e)
    | Some (At_least e) -> pr buf "{%s, ...} " (str_from_vars e)
    | None -> ()
    end;
    begin match instr with
    | Decl_const (var, exp)           -> pr buf " const %s = " var; dump_expr exp
    | Decl_mut (var, Some exp)        -> pr buf " mut %s = " var; dump_expr exp
    | Decl_mut (var, None)            -> pr buf " mut %s" var
    | Assign (var, exp)               -> pr buf " %s <- " var; dump_expr exp
    | Branch (exp, l1, l2)            -> pr buf " branch "; dump_expr exp; pr buf " %s %s" l1 l2
    | Label label                     -> pr buf "%s:" label
    | Goto label                      -> pr buf " goto %s" label
    | Print exp                       -> pr buf " print "; dump_expr exp
    | Read var                        -> pr buf " read %s" var
    | Invalidate (exp, l, vars)       -> pr buf " invalidate "; dump_expr exp;
                                         pr buf " %s [%s]" l (String.concat ", " vars)
    | Stop                            -> pr buf " stop"
    | Comment str                     -> pr buf " #%s" str
    end;
    pr buf "\n"
  in
  let b = Buffer.create 1024 in
  Array.iter2 (dump_instr b) (fst prog) (snd prog);
  Buffer.contents b

let disassemble (prog : Instr.program) =
  disassemble_annotated (prog, Array.map (fun _ -> None) prog)
