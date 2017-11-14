open Instr

exception EOF
exception Invalid_input
exception Array_is_not_a_literal

let string_of_literal : value -> string = function
  | Nil -> "nil"
  | String s -> Printf.sprintf "\"%s\"" s
  | Bool b -> string_of_bool b
  | Int n -> string_of_int n
  | Fun_ref f -> Printf.sprintf "'%s" f
  | Array arr -> raise Array_is_not_a_literal

let value_of_string str =
  try Parse.value_of_string str
  with _ -> Printf.kprintf invalid_arg "value_of_string %S" str

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
