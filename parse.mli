type parse_error =
  | Lexing of string * Lexing.position
  | Parsing of message option * Lexing.position * Lexing.position
and message = string

exception Error of parse_error
(** The two functions below may raise this exception
    -- and no other. *)

val parse_string : string -> Instr.program
val parse_file : string -> Instr.program

val report_error : parse_error -> unit
(** Prints a user-friendly error message on the standard error ouput *)
