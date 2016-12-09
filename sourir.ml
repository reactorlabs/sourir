let () =
  match Sys.argv.(1) with
  | exception _ ->
    Printf.eprintf 
      "You should provide a Sourir file to parse as command-line argument.\n\
       Example: %s test.sou\n%!"
      Sys.executable_name;
    exit 1
  | path ->
    (* TODO pretty-print the parsed file, then run it? *)
    ignore (Parse.parse_file path)
