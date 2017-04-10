open Instr

let no_line_number buf pc = ()
let line_number buf pc = Printf.bprintf buf "% 6d |" pc

let disassemble_instrs buf ?(format_pc = no_line_number) (prog : instruction_stream) =
  let dump_instr buf pc instr =
    let pr = Printf.bprintf in
    let rec dump_comma_separated how what =
      match what with
      | [] -> ()
      | [e] -> how e
      | e::t -> how e; pr buf ", "; dump_comma_separated how t
    in
    let simple buf = function
      | Var v             -> pr buf "%s" v
      | Lit lit           -> pr buf "%s" (string_of_literal lit)
    in
    let dump_expr exp =
      match exp with
      | Simple e          -> simple buf e
      | Op (Plus, [a; b]) -> pr buf "(%a + %a)" simple a simple b
      | Op (Neq,  [a; b]) -> pr buf "(%a != %a)" simple a simple b
      | Op (Eq,   [a; b]) -> pr buf "(%a == %a)" simple a simple b
      | Op ((Plus | Neq | Eq), _)         -> assert(false)
    in
    let dump_arg arg =
      match arg with
      | Arg_by_val e      -> dump_expr e
      | Arg_by_ref x      -> pr buf "&%s" x
    in
    format_pc buf pc;
    begin match instr with
    | Call (var, f, args)               ->
      pr buf " call %s = *"var;
      dump_expr f;
      pr buf " (";
      dump_comma_separated dump_arg args;
      pr buf ")"
    | Stop exp                        -> pr buf " stop "; dump_expr exp
    | Return exp                      -> pr buf " return "; dump_expr exp
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
    | Osr (exp, f, v, l, vars)        ->
      pr buf " osr ";
      dump_expr exp;
      pr buf " %s %s %s [" f v l;
      let dump_var = function
        | Osr_const (x, e) -> pr buf "const %s = " x; dump_expr e;
        | Osr_mut (x, y)   -> pr buf "mut %s = %s" x y;
        | Osr_mut_undef x  -> pr buf "mut %s" x
      in
      dump_comma_separated dump_var vars;
      pr buf "]"
    | Comment str                     -> pr buf " #%s" str
    end;
    pr buf "\n"
  in
  Array.iteri (dump_instr buf) prog

let disassemble buf (prog : Instr.program) =
  (* TODO: disassemble annotations *)
  List.iter (fun {name; formals; body} ->
      let formals = List.map (fun x -> match x with
          | Mut_ref_param x -> "mut "^x
          | Const_val_param x -> "const "^x) formals in
      let formals = String.concat ", " formals in
      Printf.bprintf buf "function %s (%s)\n" name formals;
      List.iter (fun version ->
          Printf.bprintf buf "version %s\n" version.label;
          disassemble_instrs buf version.instrs) body
    ) (prog.main :: prog.functions)

let disassemble_s (prog : Instr.program) =
  let b = Buffer.create 1024 in
  disassemble b prog;
  Buffer.to_bytes b

let disassemble_o outchan (prog : Instr.program) =
  let b = Buffer.create 1024 in
  disassemble b prog;
  Buffer.output_buffer outchan b

let disassemble_instrs_s (prog : instruction_stream) =
  let b = Buffer.create 1024 in
  disassemble_instrs b prog;
  Buffer.to_bytes b

let pretty_print_version outchan (name, version) =
  let b = Buffer.create 1024 in
  Printf.bprintf b "version %s\n" name;
  disassemble_instrs b ~format_pc:line_number version;
  Buffer.output_buffer outchan b

let pretty_print outchan prog =
  List.iter (pretty_print_version outchan) prog
