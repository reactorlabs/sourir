open OUnit;;
open Sourir;;

let run prog () =
  let res = run_bounded (prog, List.length (prog)) in
    assert (stop res)

let rec do_assemble (prog, i) =
  match prog with
  | [] -> []
  | cur :: tail -> (i, cur) :: do_assemble (tail, i+1)

let assemble prog = do_assemble (prog, 1)

let test_print = assemble [
    (Print (Lit (Int 1)));
    (Print (Lit (Int 2)));
    (Stop)
  ]

let test_decl_const = assemble [
    (Decl_const ("x", Lit (Int 1)));
    (Print (Var "x"));
    (Stop)
  ]

let test_mut = assemble [
    (Decl_mut ("x", Lit (Int 1)));
    (Print (Var "x"));
    (Assign ("x", Lit (Int 2)));
    (Print (Var "x"));
    (Stop)
  ]

let suite =
  "suite">:::
  ["mut">:: run test_mut;
   "decl_const">:: run test_decl_const;
   "print">:: run test_print;]
;;

let _ =
    run_test_tt_main suite
;;
