%token NIL
%token<bool> BOOL
%token<int> INT
%token<string> IDENTIFIER
%token DOUBLE_EQUAL NOT_EQUAL PLUS /* MINUS TIMES LT LTE GT GTE */
%token LPAREN RPAREN LBRACKET RBRACKET LBRACE RBRACE
%token COLON EQUAL LEFTARROW TRIPLE_DOT COMMA
%token CONST MUT BRANCH GOTO PRINT OSR STOP READ DROP CLEAR VERSION FUNCTION
%token<string> COMMENT
%token NEWLINE
%token EOF

%start<Instr.program> program

%{ open Instr

let scope_annotation (mode, xs) =
  let xs = Instr.VarSet.of_list xs in
  match mode with
  | `Exact -> Instr.ExactScope xs
  | `At_least -> Instr.AtLeastScope xs
%}


%%

program: optional_newlines prog=program_code EOF { prog }

program_code:
| l1=instruction_line prog=list(instruction_line) fs=list(afunction)
  {
    let annotations, instructions = List.split prog in
    let a1, i1 = l1 in
    { main = {
          name = "main";
          formals = [];
          body = [("anon", Array.of_list (i1::instructions))];
          annotations = [("anon", Array.of_list (a1::annotations))]; };
      functions = fs;
    }
  }
| f1=afunction fs=list(afunction)
  {
    let fs = f1 :: fs in
    let main = (try List.find (fun {name = n} -> n = "main") fs with
        | Not_found -> (Printf.printf ("missing main function\n"); exit 1)
      ) in
    let rest = List.filter (fun {name = n} -> n <> "main") fs in
    { main = main;
      functions = rest; }
  }

formal_param:
| CONST x=variable
    { ParamConst x }
| MUT x=variable
    { ParamMut x }

afunction:
| FUNCTION name=variable LPAREN formals=list(formal_param) RPAREN NEWLINE optional_newlines prog=list(instruction_line)
  {
    let annotations, instructions = List.split prog in
    { name = name;
      formals = formals;
      body = [("anon", Array.of_list instructions)];
      annotations = [("anon", Array.of_list annotations)]; }
  }
| FUNCTION name=variable LPAREN formals=list(formal_param) RPAREN NEWLINE optional_newlines v1=version vs=list(version)
  {
    let vs = v1 :: vs in
    let bodies, annots = List.split vs in
    { name = name;
      formals = formals;
      body = bodies;
      annotations = annots; }
  }

version:
| VERSION label=variable NEWLINE optional_newlines prog=list(instruction_line)
  {
    let annotations, instructions = List.split prog in
    ((label, Array.of_list instructions),
     (label, Array.of_list annotations))
  }

instruction_line:
| a=scope_annotation i=instruction NEWLINE optional_newlines { (a, i) }

scope_annotation:
| { None }
| annot=delimited(LBRACE, scope, RBRACE) optional_newlines { Some (scope_annotation annot) }

optional_newlines: list(NEWLINE) { () }

scope:
| x=variable COMMA sc=scope { let (mode, xs) = sc in (mode, x::xs) }
| x=variable { (`Exact, [x]) }
| { (`Exact, []) }
| TRIPLE_DOT { (`At_least, []) }

osr_def:
| CONST x=variable EQUAL e=expression
    { OsrConst (x, e) }
| MUT x=variable
    { OsrMutUndef x }
| MUT x=variable EQUAL y=variable
    { OsrMut (x, y) }

instruction:
| CONST x=variable EQUAL e=expression
  { Decl_const (x, e) }
| MUT x=variable
  { Decl_mut (x, None) }
| MUT x=variable EQUAL e=expression
  { Decl_mut (x, Some e) }
| x=variable LEFTARROW e=expression
  { Assign (x, e) }
| BRANCH e=expression l1=label l2=label
  { Branch (e, l1, l2) }
| l=label COLON
  { Label l }
| GOTO l=label
  { Goto l }
| READ x=variable
  { Read x }
| DROP x=variable
  { Drop x }
| CLEAR x=variable
  { Clear x }
| PRINT e=expression
  { Print e }
| OSR
  e=expression f=label v=label l=label LBRACKET xs=separated_list(COMMA, osr_def) RBRACKET
  { Osr (e, f, v, l, xs) }
| STOP
  { Stop }
| s=COMMENT
  { Comment s }

simple_expression:
  | lit=lit { Lit lit }
  | x=variable { Var x }

expression:
  | e = simple_expression { Simple e }
  | LPAREN e1=simple_expression op=infixop e2=simple_expression RPAREN
    { Op (op, [e1;e2]) }

label: id=IDENTIFIER { (id : Label.t) }
variable: id=IDENTIFIER { (id : Variable.t) }

infixop:
  | DOUBLE_EQUAL { Eq }
  | NOT_EQUAL { Neq }
  | PLUS { Plus }
  (* | MINUS { Sub } *)
  (* | TIMES { Mult } *)
  (* | LT { Lt } *)
  (* | LTE { Lte } *)
  (* | GT { Gt } *)
  (* | GTE { Gte } *)

lit:
  | NIL { (Nil : litteral) }
  | b=BOOL { (Bool b : litteral) }
  | n=INT { (Int n : litteral) }
