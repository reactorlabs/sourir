{
open Lexing
open Parser

exception Lexing_error of string

let keyword_table = [
  "const", CONST;
  "mut", MUT;
  "branch", BRANCH;
  "goto", GOTO;
  "print", PRINT;
  "invalidate", INVALIDATE;
  "stop", STOP;
]

let id_or_keyword id =
  match List.assoc id keyword_table with
  | exception Not_found -> IDENTIFIER id
  | kwd -> kwd

let comment_of_string str =
  let buf = Buffer.create 10 in
  String.iter (function
      | '\r' -> ()
      | c -> Buffer.add_char buf c) str;
  Buffer.contents buf

let lexing_error lexbuf =
  let invalid_input = String.make 1 (Lexing.lexeme_char lexbuf 0) in
  raise (Lexing_error invalid_input)
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
  | "+" { PLUS }
  | "[" { LBRACKET }
  | "]" { RBRACKET }
  | "(" { LPAREN }
  | ")" { RPAREN }
  | "{" { LBRACE }
  | "}" { RBRACE }
  | "," { COMMA }
  | "..." { TRIPLE_DOT }
  | ":" { COLON }
  | "=" { EQUAL }
  | "<-" { LEFTARROW }
  | eof { EOF }
  | _ { lexing_error lexbuf }
