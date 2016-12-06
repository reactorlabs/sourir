%token NIL
%token<bool> BOOL
%token<int> INT
%token<Ast.variable> VARIABLE
%token<Ast.label> LABEL
%token DOUBLE_EQUAL (* PLUS MINUS TIMES LT LTE GT GTE *)
%token LBRACKET RBRACKET
%token COLON
%token CONST MUT EQUAL LEFTARROW BRANCH GOTO PRINT INVALIDATE STOP
%token NEWLINE
%token EOF

%start <Ast.program> program

%{ open Ast %}

%%

program:
| prog=list(labeled_instruction) EOF { prog }

labeled_instruction:
| l=line_label i=instruction NEWLINE { (l, i) }

line_label:
| l=LABEL COLON option(NEWLINE) { l }

instruction:
| CONST x=VARIABLE EQUAL e=expression
  { Decl_const (x, e) }
| MUT x=VARIABLE EQUAL e=expression
  { Decl_mut (x, e) }
| x=VARIABLE LEFTARROW e=expression
  { Assign (x, e) }
| BRANCH e=expression l1=LABEL l2=LABEL
  { Branch (e, l1, l2) }
| GOTO l=LABEL
  { Goto l }
| PRINT e=expression
  { Print e }
| INVALIDATE
  e=expression l=LABEL
  xs=delimited(LBRACKET, list(VARIABLE), RBRACKET)
  { Invalidate (e, l, xs) }
| STOP
  { Stop }

expression:
  | lit=lit { Lit lit }
  | x=VARIABLE { Var x }
  | x=VARIABLE op=infixop y=VARIABLE { Op (op, [x;y]) }

infixop:
  | DOUBLE_EQUAL { Eq }
  (* | PLUS { Add } *)
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
