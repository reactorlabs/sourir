open Instr

let disassemble_segment b (prog : segment) =
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
    | Drop var                        -> pr buf " drop %s" var
    | Clear var                       -> pr buf " clear %s" var
    | Assign (var, exp)               -> pr buf " %s <- " var; dump_expr exp
    | Branch (exp, l1, l2)            -> pr buf " branch "; dump_expr exp; pr buf " %s %s" l1 l2
    | Label label                     -> pr buf "%s:" label
    | Goto label                      -> pr buf " goto %s" label
    | Print exp                       -> pr buf " print "; dump_expr exp
    | Read var                        -> pr buf " read %s" var
    | Osr (exp, v, l, vars)           ->
      pr buf " osr ";
      dump_expr exp;
      pr buf " %s %s [" v l;
      let last = (List.length vars) - 1 in
      List.iteri (fun i x ->
          begin match x with
            | OsrConst (x, e) -> pr buf "const %s = " x; dump_expr e;
            | OsrMut (x, OsrExp e) -> pr buf "mut %s = " x; dump_expr e;
            | OsrMut (x, OsrUndef) -> pr buf "mut %s" x
          end;
          if (i < last) then pr buf ", "
        ) vars;
      pr buf "]"
    | Stop                            -> pr buf " stop"
    | Comment str                     -> pr buf " #%s" str
    end;
    pr buf "\n"
  in
  Array.iter2 (dump_instr b) (fst prog) (snd prog)

let disassemble (prog : Instr.program_) =
  let b = Buffer.create 1024 in
  List.iter (fun (name, segment) ->
      Printf.bprintf b "segment %s\n" name;
      disassemble_segment b segment) prog;
  Buffer.contents b

let disassemble_instr (instr : Instr.instruction_stream) =
  let b = Buffer.create 1024 in
  Printf.bprintf b "segment _anonym\n";
  disassemble_segment b (instr, Array.map (fun _ -> None) instr);
  Buffer.contents b
