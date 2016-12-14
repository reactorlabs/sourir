open Instr

exception EOF
exception Invalid_input

type input = unit -> input_tape (* may raise one of the exceptions above *)
and input_tape = Next of value * input

let no_input () = raise EOF

let rec list_input li () = match li with
  | [] -> raise EOF
  | v :: vs -> Next (v, list_input vs)

let rec stdin_input () =
  match value_of_string (read_line ()) with
  | exception End_of_file -> raise EOF
  | exception (Invalid_argument _) -> raise Invalid_input
  | value -> Next (value, stdin_input)
