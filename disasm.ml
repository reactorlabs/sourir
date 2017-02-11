open Instr

let no_line_number buf pc = ()
let line_number buf pc = Printf.bprintf buf "% 6d |" pc

let disassemble_segment buf ?(format_pc = no_line_number) (prog : segment) =
  let dump_instr buf pc instr =
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
    format_pc buf pc;
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
      let rec dump_vars vs =
        let dump_var = function
          | OsrConst (x, e) -> pr buf "const %s = " x; dump_expr e;
          | OsrMut (x, y) -> pr buf "mut %s = %s" x y;
          | OsrMutUndef x -> pr buf "mut %s" x
        in
        match vs with
          | [] -> ()
          | hd :: [] -> dump_var hd
          | hd :: tail -> dump_var hd; pr buf ", "; dump_vars tail
      in
      dump_vars vars;
      pr buf "]"
    | Stop                            -> pr buf " stop"
    | Comment str                     -> pr buf " #%s" str
    end;
    pr buf "\n"
  in
  Array.iteri (dump_instr buf) prog

let disassemble (prog : Instr.program) =
  let b = Buffer.create 1024 in
  List.iter (fun (name, segment) ->
      Printf.bprintf b "segment %s\n" name;
      disassemble_segment b segment) prog;
  Buffer.contents b

let disassemble_instr (instr : Instr.instruction_stream) =
  let b = Buffer.create 1024 in
  Printf.bprintf b "segment _anonym\n";
  disassemble_segment b instr;
  Buffer.contents b

let pretty_print_segment outchan (name, segment) =
  let b = Buffer.create 1024 in
  Printf.bprintf b "segment %s\n" name;
  disassemble_segment b ~format_pc:line_number segment;
  Buffer.output_buffer outchan b

let pretty_print outchan prog =
  List.iter (pretty_print_segment outchan) prog
