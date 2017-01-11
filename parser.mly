%token NIL
%token<bool> BOOL
%token<int> INT
%token<string> IDENTIFIER
%token DOUBLE_EQUAL NOT_EQUAL PLUS /* MINUS TIMES LT LTE GT GTE */
%token LPAREN RPAREN LBRACKET RBRACKET LBRACE RBRACE
%token COLON EQUAL LEFTARROW TRIPLE_DOT COMMA
%token CONST MUT BRANCH GOTO PRINT INVALIDATE STOP READ
%token<string> COMMENT
%token NEWLINE
%token EOF

%start<Instr.annotated_program> program

%{ open Instr

let scope_annotation (mode, xs) =
  let xs = Instr.VarSet.of_list xs in
  match mode with
  | `Exact -> Exact xs
  | `At_least -> At_least xs
%}


%%

program:
| optional_newlines prog=list(instruction_line) EOF
  {
    let annotations, instructions = List.split prog in
    (Array.of_list instructions,
     Array.of_list annotations)
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
| TRIPLE_DOT { (`At_least, []) }

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
| PRINT e=expression
  { Print e }
| INVALIDATE
  e=expression l=label
  xs=delimited(LBRACKET, separated_list(COMMA, variable), RBRACKET)
  { Invalidate (e, l, xs) }
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
