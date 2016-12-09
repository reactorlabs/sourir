%token NIL
%token<bool> BOOL
%token<int> INT
%token<string> IDENTIFIER
%token DOUBLE_EQUAL PLUS /* MINUS TIMES LT LTE GT GTE */
%token LPAREN RPAREN LBRACKET RBRACKET
%token COLON EQUAL LEFTARROW
%token CONST MUT BRANCH GOTO PRINT INVALIDATE STOP
%token<string> COMMENT
%token NEWLINE
%token EOF

%start<Instr.program> program

%{ open Instr %}


%%

program:
| prog=list(instruction_line) EOF { Array.of_list prog }

instruction_line:
| i=instruction NEWLINE { i }

instruction:
| CONST x=variable EQUAL e=expression
  { Decl_const (x, e) }
| MUT x=variable EQUAL e=expression
  { Decl_mut (x, e) }
| x=variable LEFTARROW e=expression
  { Assign (x, e) }
| BRANCH e=expression l1=label l2=label
  { Branch (e, l1, l2) }
| l=label COLON
  { Label l }
| GOTO l=label
  { Goto l }
| PRINT e=expression
  { Print e }
| INVALIDATE
  e=expression l=label
  xs=delimited(LBRACKET, list(variable), RBRACKET)
  { Invalidate (e, l, xs) }
| STOP
  { Stop }
| s=COMMENT
  { Comment s }

expression:
  | lit=lit { Lit lit }
  | x=variable { Var x }
  | LPAREN x=variable op=infixop y=variable RPAREN  { Op (op, [x;y]) }

label: id=IDENTIFIER { (id : Label.t) }
variable: id=IDENTIFIER { (id : Variable.t) }

infixop:
  | DOUBLE_EQUAL { Eq }
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
