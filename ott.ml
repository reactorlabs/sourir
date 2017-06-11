open Instr

let no_line_number buf pc = ()
let line_number buf pc = Printf.bprintf buf "% 6d |" pc

let pr = Printf.bprintf

let rec dump_comma_separated how buf what =
  match what with
  | [] -> ()
  | [e] -> how buf e
  | e::t -> pr buf "%a, %a" how e (dump_comma_separated how) t

let disassemble_instrs buf (instrs : instructions) =
  let rec dump_instr buf pc needs_label =
    if pc = Array.length instrs then ()
    else begin
      let dump_next_instr () = dump_instr buf (pc+1) true in
      let simple buf = function
        | Var v             -> pr buf "%s" v
        | Constant c        -> pr buf "%s" (IO.string_of_value c)
      in
      let dump_expr buf exp =
        match exp with
        | Simple e           -> simple buf e
        | Unop (Neg, a)      -> pr buf "(-%a)"      simple a
        | Unop (Not, a)      -> pr buf "(!%a)"      simple a
        | Binop (Plus, a, b) -> pr buf "(%a + %a)"  simple a simple b
        | Binop (Sub,  a, b) -> pr buf "(%a - %a)"  simple a simple b
        | Binop (Mult, a, b) -> pr buf "(%a * %a)"  simple a simple b
        | Binop (Div,  a, b) -> pr buf "(%a / %a)"  simple a simple b
        | Binop (Mod,  a, b) -> pr buf "(%a %% %a)" simple a simple b
        | Binop (Eq,   a, b) -> pr buf "(%a == %a)" simple a simple b
        | Binop (Neq,  a, b) -> pr buf "(%a != %a)" simple a simple b
        | Binop (Lt,   a, b) -> pr buf "(%a < %a)"  simple a simple b
        | Binop (Lte,  a, b) -> pr buf "(%a <= %a)" simple a simple b
        | Binop (Gt,   a, b) -> pr buf "(%a > %a)"  simple a simple b
        | Binop (Gte,  a, b) -> pr buf "(%a >= %a)" simple a simple b
        | Binop (And,  a, b) -> pr buf "(%a && %a)" simple a simple b
        | Binop (Or,   a, b) -> pr buf "(%a || %a)" simple a simple b
        | Array_index (a, i) -> pr buf "%s[%a]"     a simple i
        | Array_length e     -> pr buf "length(%a)" simple e
      in
      let dump_arg buf arg = dump_expr buf arg in
      let print_pc_label () = pr buf "%d : " pc in
      let print_label label =
        let label = if String.length label = 1 then "l"^label else label in
        pr buf "%s : " label in
      begin match[@warning "-4"] instrs.(pc) with
      | Label _ | Osr _ ->
        ()
      | _ ->
        if needs_label then print_pc_label ()
      end;
      begin match instrs.(pc) with
      | Call (var, f, args)               ->
        pr buf " call %s = "var;
        dump_expr buf f;
        pr buf " (%a)\n" (dump_comma_separated dump_arg) args;
        dump_next_instr ()
      | Stop exp                        ->
        pr buf " stop %a\n" dump_expr exp;
        dump_next_instr ()
      | Return exp                      ->
        pr buf " return %a\n" dump_expr exp;
        dump_next_instr ()
      | Decl_var (var, exp)             ->
        pr buf " var %s = %a\n" var dump_expr exp;
        dump_next_instr ()
      | Decl_array (var, Length exp)    ->
        pr buf " array %s[%a]\n" var dump_expr exp;
        dump_next_instr ()
      | Decl_array (var, List li)       ->
        pr buf " array %s = [%a]\n" var (dump_comma_separated dump_expr) li;
        dump_next_instr ()
      | Drop var                        ->
        pr buf " drop %s\n" var;
        dump_next_instr ()
      | Assign (var, exp)               ->
        pr buf " %s <- %a\n" var dump_expr exp;
        dump_next_instr ()
      | Array_assign (var, index, exp)  ->
        pr buf " %s[%a] <- %a\n" var dump_expr index dump_expr exp;
        dump_next_instr ()
      | Branch (exp, l1, l2)            ->
        pr buf " branch %a %s %s\n" dump_expr exp l1 l2;
        dump_next_instr ()
      | Label (MergeLabel l | BranchLabel l) ->
        print_label l;
        dump_instr buf (pc+1) false
      | Goto label                      ->
        pr buf " goto %s\n" label;
        dump_next_instr ()
      | Print exp                       ->
        pr buf " print %a\n" dump_expr exp;
        dump_next_instr ()
      | Assert exp                      ->
        pr buf " assert %a\n" dump_expr exp;
        dump_next_instr ()
      | Read var                        ->
        pr buf " read %s\n" var;
        dump_next_instr ()
      | Osr {label; cond; target={func; version; pos}; varmap; frame_maps} ->
        print_label label;
        let dump_var buf = function
          | Osr_var (x, e)     -> pr buf "%s = %a" x dump_expr e
        in
        let dump_frame buf {cont_pos={func; version; pos}; cont_res; varmap} =
          pr buf "(%s, %s, %s) [%s = $, %a]"
              func version pos
              cont_res
              (dump_comma_separated dump_var) varmap
        in
        pr buf "osr %a , (%s, %s, %s) [%a], %a\n"
          (dump_comma_separated dump_expr) cond
          func version pos
          (dump_comma_separated dump_var) varmap
          (dump_comma_separated dump_frame) frame_maps;
        dump_next_instr ()
      | Comment str                     ->
        dump_next_instr ()
      end;
    end
  in
  dump_instr buf 0 true

let disassemble buf (prog : Instr.program) =
  let dump_func buf {name; formals; body} =
      let print_formal buf (Param x) = pr buf "%s " x in
      let print_formals buf = (dump_comma_separated print_formal) buf formals in
      Printf.bprintf buf "%s -> ( %t ) ( " name print_formals;
      let dump_vers buf version =
          pr buf "%s -> (\n" version.label;
          disassemble_instrs buf version.instrs;
          pr buf ") "
      in
      (dump_comma_separated dump_vers) buf body;
      Printf.bprintf buf " ) ";
  in
  Printf.bprintf buf "P( ";
  (dump_comma_separated dump_func) buf (prog.main :: prog.functions);
  Printf.bprintf buf ")\n"

let disassemble_s (prog : Instr.program) =
  let b = Buffer.create 1024 in
  disassemble b prog;
  Buffer.to_bytes b

let disassemble_o outchan (prog : Instr.program) =
  let b = Buffer.create 1024 in
  disassemble b prog;
  Buffer.output_buffer outchan b;
  flush outchan
