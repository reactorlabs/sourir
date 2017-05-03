open Instr

exception EOF
exception Invalid_input

let rec string_of_value : value -> string = function
  | Nil -> "nil"
  | Bool b -> string_of_bool b
  | Int n -> string_of_int n
  | Fun_ref f -> "'" ^ f
  | Array vs ->
    let ss = Array.to_list (Array.map string_of_value vs) in
    "[" ^ String.concat ", " ss ^ "]"

let value_of_string : string -> value = function
  | "nil" -> Nil
  | "true" -> Bool true
  | "false" -> Bool false
  (* Should we allow function literals as user input? *)
  | n ->
    try Int (int_of_string n) with _ ->
      Printf.kprintf invalid_arg "value_of_string %S" n
(* TODO add case for array *)

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
