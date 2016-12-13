let position {Lexing.pos_fname; pos_lnum; pos_cnum; pos_bol} =
  let file = pos_fname in
  let line = pos_lnum in
  let character = pos_cnum - pos_bol in
  (file, line, character)

let parse_string str =
  let lexbuf = Lexing.from_string str in
  Parser.program Lexer.token lexbuf

let parse_file path =
  let chan = open_in path in
  let lexbuf =
    let open Lexing in
    let lexbuf = from_channel chan in
    lexbuf.lex_start_p <- {
      pos_fname = path;
      pos_lnum = 1;
      pos_bol = 0;
      pos_cnum = 0;
    };
    lexbuf.lex_curr_p <- lexbuf.lex_start_p;
    lexbuf
  in
  match Parser.program Lexer.token lexbuf with
  | program -> program
  | exception (Lexer.Lexing_error invalid_input) ->
    let file, line, character = position lexbuf.Lexing.lex_curr_p in
    Printf.eprintf
      "File %S, line %d, character %d:\nLexing error: invalid input %S\n%!"
      file line character invalid_input;
    exit 1
  | exception Parser.Error ->
    let file, start_line, start_character = position lexbuf.Lexing.lex_start_p in
    let _, curr_line, curr_character = position lexbuf.Lexing.lex_curr_p in
    let open Printf in
    let lines =
      if curr_line = start_line
      then sprintf "line %d" curr_line
      else sprintf "lines %d-%d" start_line curr_line in
    let characters =
      if curr_line = start_line
      then sprintf "characters %d-%d" start_character curr_character
      else sprintf "character %d" start_character in
    Printf.eprintf "File %S, %s, %s:\nParsing error\n%!"
      file lines characters;
    exit 2
