open Instr

let no_line_number buf pc = ()
let line_number buf pc = Printf.bprintf buf "% 6d |" pc

let pr = Printf.bprintf

let rec dump_comma_separated how buf what =
  match what with
  | [] -> ()
  | [e] -> how buf e
  | e::t -> pr buf "%a, %a" how e (dump_comma_separated how) t

let disassemble_instrs buf ?(format_pc = no_line_number) (prog : instructions) =
  let dump_instr buf pc instr =
    let simple buf = function
      | Var v             -> pr buf "%s" v
      | Constant c        -> pr buf "%s" (IO.string_of_value c)
    in
    let dump_expr buf exp =
      match exp with
      | Simple e          -> simple buf e
      | Op (Neg,  [a])    -> pr buf "(-%a)"      simple a
      | Op (Plus, [a; b]) -> pr buf "(%a + %a)"  simple a simple b
      | Op (Sub,  [a; b]) -> pr buf "(%a - %a)"  simple a simple b
      | Op (Mult, [a; b]) -> pr buf "(%a * %a)"  simple a simple b
      | Op (Div,  [a; b]) -> pr buf "(%a / %a)"  simple a simple b
      | Op (Mod,  [a; b]) -> pr buf "(%a %% %a)" simple a simple b
      | Op (Eq,   [a; b]) -> pr buf "(%a == %a)" simple a simple b
      | Op (Neq,  [a; b]) -> pr buf "(%a != %a)" simple a simple b
      | Op (Lt,   [a; b]) -> pr buf "(%a < %a)"  simple a simple b
      | Op (Lte,  [a; b]) -> pr buf "(%a <= %a)" simple a simple b
      | Op (Gt,   [a; b]) -> pr buf "(%a > %a)"  simple a simple b
      | Op (Gte,  [a; b]) -> pr buf "(%a >= %a)" simple a simple b
      | Op (Not,  [a])    -> pr buf "(!%a)"      simple a
      | Op (And,  [a; b]) -> pr buf "(%a && %a)" simple a simple b
      | Op (Or,   [a; b]) -> pr buf "(%a || %a)" simple a simple b
      | Op ((Neg | Plus | Sub | Mult | Div | Mod), _)
      | Op ((Eq | Neq | Lt | Lte | Gt | Gte), _)
      | Op ((Not | And | Or), _) -> assert(false)
      | Op (Array_index, [array; index]) -> pr buf "%a[%a]" simple array simple index
      | Op (Array_length, [array]) -> pr buf "length(%a)" simple array
      | Op ((Array_index | Array_length), _) -> assert(false)
    in
    let dump_arg buf arg = dump_expr buf arg in
    format_pc buf pc;
    begin match instr with
    | Call (var, f, args)               ->
      pr buf " call %s = "var;
      dump_expr buf f;
      pr buf " (%a)" (dump_comma_separated dump_arg) args;
    | Stop exp                        -> pr buf " stop %a" dump_expr exp
    | Return exp                      -> pr buf " return %a" dump_expr exp
    | Decl_var (var, exp)           -> pr buf " var %s = %a" var dump_expr exp
    | Decl_array (var, Length exp)    -> pr buf " array %s[%a]" var dump_expr exp
    | Decl_array (var, List li)       -> pr buf " array %s = [%a]" var
                                           (dump_comma_separated dump_expr) li
    | Drop var                        -> pr buf " drop %s" var
    | Assign (var, exp)               -> pr buf " %s <- %a" var dump_expr exp
    | Array_assign (var, index, exp)  -> pr buf " %s[%a] <- %a" var dump_expr index dump_expr exp
    | Branch (exp, l1, l2)            -> pr buf " branch %a $%s $%s" dump_expr exp l1 l2
    | Label (MergeLabel label)        -> pr buf "%s:" label
    | Label (BranchLabel label)        -> pr buf "$%s:" label
    | Goto label                      -> pr buf " goto %s" label
    | Print exp                       -> pr buf " print %a" dump_expr exp
    | Assert exp                      -> pr buf " assert %a" dump_expr exp
    | Read var                        -> pr buf " read %s" var
    | Osr {label; cond; target = {func; version; pos}; map} ->
      let dump_var buf = function
        | Osr_var (x, e)     -> pr buf "var %s = %a" x dump_expr e
      in
      pr buf " osr %s [%a] (%s, %s, %s) [%a]"
        label
        (dump_comma_separated dump_expr) cond
        func version pos
        (dump_comma_separated dump_var) map
    | Comment str                     -> pr buf " #%s" str
    end;
    pr buf "\n"
  in
  Array.iteri (dump_instr buf) prog

let disassemble buf (prog : Instr.program) =
  (* TODO: disassemble annotations *)
  List.iter (fun {name; formals; body} ->
      let print_formal buf (Param x) = pr buf "var %s" x in
      let print_formals buf = (dump_comma_separated print_formal) buf formals in
      Printf.bprintf buf "function %s (%t)\n" name print_formals;
      List.iter (fun version ->
          pr buf "version %s\n" version.label;
          disassemble_instrs buf version.instrs) body
    ) (prog.main :: prog.functions)

let disassemble_s (prog : Instr.program) =
  let b = Buffer.create 1024 in
  disassemble b prog;
  Buffer.to_bytes b

let disassemble_o outchan (prog : Instr.program) =
  let b = Buffer.create 1024 in
  disassemble b prog;
  Buffer.output_buffer outchan b;
  flush outchan

let disassemble_instrs_s (prog : instructions) =
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
