open OUnit;;
open Sourir;;

let run prog () =
  let res = run_bounded (prog, Array.length prog) in
    assert (stop res)

let test_print = let open Assembler in assemble
[|
  print_i 1;
  print_i 2;
  stop
|]

let test_decl_const = let open Assembler in assemble
[|
  const x 1;
  print x;
  stop;
|]

let test_mut = let open Assembler in assemble
[|
  mut x 1;
  print x;
  assign x 2;
  print x;
  stop;
|]

let suite =
  "suite">:::
  ["mut">:: run test_mut;
   "decl_const">:: run test_decl_const;
   "print">:: run test_print;]
;;

let _ =
    run_test_tt_main suite
;;
