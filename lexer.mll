{
open Parser

exception Error of string * Lexing.position

let keyword_table = [
  "var", VAR;
  "branch", BRANCH;
  "goto", GOTO;
  "print", PRINT;
  "assert", ASSERT;
  "osr", OSR;
  "stop", STOP;
  "read", READ;
  "drop", DROP;
  "return", RETURN;
  "call", CALL;
  "version", VERSION;
  "function", FUNCTION;
  "array", ARRAY;
  "length", LENGTH;
]

let id_or_keyword id =
  match List.assoc id keyword_table with
  | exception Not_found -> IDENTIFIER id
  | kwd -> kwd

let comment_of_string str =
  let buf = Buffer.create 10 in
  (* start at 1: skip the '#' character *)
  for i = 1 to String.length str - 1 do
    if str.[i] <> '\r'
    then Buffer.add_char buf str.[i];
  done;
  Buffer.contents buf

let lexing_error lexbuf =
  let invalid_input = String.make 1 (Lexing.lexeme_char lexbuf 0) in
  raise (Error (invalid_input, lexbuf.Lexing.lex_curr_p))
}

let int_literal = '-'? ['0'-'9'] ['0'-'9']*
let blank = [' ' '\t']+
let newline = ('\r'* '\n')
let id = ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_']*

rule token = parse
  | newline { Lexing.new_line lexbuf; NEWLINE }
  | blank+ { token lexbuf }
  | int_literal { INT (int_of_string (Lexing.lexeme lexbuf)) }
  | "#" [^ '\n']* { COMMENT (comment_of_string (Lexing.lexeme lexbuf)) }
  | "nil" { NIL }
  | "true" { BOOL true }
  | "false" { BOOL false }
  | id { id_or_keyword (Lexing.lexeme lexbuf) }
  | "==" { DOUBLE_EQUAL }
  | "!=" { NOT_EQUAL }
  | "<" { LT }
  | "<=" { LTE }
  | ">" { GT }
  | ">=" { GTE }
  | "+" { PLUS }
  | "-" { MINUS }
  | "*" { TIMES }
  | "/" { DIVIDE }
  | "%" { MOD }
  | "&&" { DOUBLE_AMP }
  | "||" { DOUBLE_PIPE }
  | "!" { BANG }
  | "[" { LBRACKET }
  | "]" { RBRACKET }
  | "(" { LPAREN }
  | ")" { RPAREN }
  | "{" { LBRACE }
  | "}" { RBRACE }
  | "," { COMMA }
  | "..." { TRIPLE_DOT }
  | ":" { COLON }
  | "$" { DOLLAR }
  | "=" { EQUAL }
  | "<-" { LEFTARROW }
  | "'" { SINGLE_QUOTE }
  | eof { EOF }
  | _ { lexing_error lexbuf }
