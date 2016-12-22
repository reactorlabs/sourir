let position {Lexing.pos_fname; pos_lnum; pos_cnum; pos_bol} =
  let file = pos_fname in
  let line = pos_lnum in
  let character = pos_cnum - pos_bol in
  (file, line, character)

let split_annotations program =
  let annotations = Array.map fst program in
  let instructions = Array.map snd program in
  (instructions, annotations)

exception Parse_error of string option * Lexing.position * Lexing.position

let parse lexbuf =
  (* see the Menhir manual for the description of
     error messages support *)
  let open MenhirLib.General in
  let module Interp = Parser.MenhirInterpreter in
  let input = Interp.lexer_lexbuf_to_supplier Lexer.token lexbuf in
  let success prog = split_annotations prog in
  let failure error_state =
    let env = match error_state with
      | Interp.HandlingError env -> env
      | _ -> assert false in
    match Interp.stack env with
    | lazy Nil -> assert false
    | lazy (Cons (Interp.Element (state, _, start_pos, end_pos), _)) ->
      let message =
        try Some (Parser_messages.message (Interp.number state)) with
        | Not_found -> None in
      raise (Parse_error (message, start_pos, end_pos))
  in
  Interp.loop_handle success failure input
    (Parser.Incremental.program lexbuf.Lexing.lex_curr_p)

let parse_string str =
  let lexbuf = Lexing.from_string str in
  parse lexbuf

let parse_file path : Scope.annotated_program =
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
  try parse lexbuf with
  | Parse_error (message, start_pos, end_pos) ->
    let file, start_line, start_character = position start_pos in
    let _, curr_line, curr_character = position end_pos in
    let open Printf in
    let lines =
      if curr_line = start_line
      then sprintf "line %d" curr_line
      else sprintf "lines %d-%d" start_line curr_line in
    let characters =
      if curr_line = start_line
      then sprintf "characters %d-%d" start_character curr_character
      else sprintf "character %d" start_character in
    Printf.eprintf "File %S, %s, %s, parsing error:\n%!"
      file lines characters;
    begin match message with
    | None -> ()
    | Some error_message -> prerr_endline error_message
    end;
    exit 2
  | Lexer.Lexing_error invalid_input ->
    let file, line, character = position lexbuf.Lexing.lex_curr_p in
    Printf.eprintf
      "File %S, line %d, character %d, lexing error:\nInvalid input %S\n%!"
      file line character invalid_input;
    exit 1
