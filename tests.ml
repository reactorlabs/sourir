open OUnit
open Ast
open Eval

let ok _ = true

let trace_is li =
  fun conf -> read_trace conf = li
let has_var x v =
  fun conf -> (lookup conf.heap conf.env x = v)

let (&&&) p1 p2 conf = (p1 conf) && (p2 conf)

let run prog pred () =
  let final_conf = run_forever prog in
  assert (pred final_conf)

let test_print =
  let open Assembler in
  assemble Instr.[|
    print_i 1;
    print_i 2;
    stop
  |]

let test_decl_const =
  let open Assembler in
  assemble Instr.[|
    const x 1;
    print x;
    stop;
  |]

let test_mut =
  let open Assembler in
  assemble Instr.[|
    mut_i x 1;
    print x;
    assign x 2;
    print x;
    stop;
  |]

let test_jump =
  let open Assembler in
  assemble Instr.[|
    mut_b x true;
    goto "jump";
    assign_b x false;
    label "jump";
  |]

let test_overloading =
  let open Assembler.OO in
  let b, x, y = bool_var "b", int_var "x", int_var "y" in
  Assembler.assemble [|
    mut b (bool true);
    mut x (int 1);
    const y x;
    goto "jump";
    assign b (bool false);
    label "jump";
    assign x (int 2);
  |]

let suite =
  let open Assembler in
  "suite">:::
  ["mut">:: run test_mut
     (has_var x (Value.int 2)
      &&& (trace_is Value.[int 1; int 2]));
   "decl_const">:: run test_decl_const
     (has_var x (Value.int 1));
   "print">:: run test_print
     (trace_is Value.[int 1; int 2]);
   "jump">:: run test_jump (has_var x (Value.bool true));
   "jump (oo)" >:: run test_overloading
     (has_var "b" (Value.bool true)
      &&& has_var "x" (Value.int 2)
      &&& has_var "y" (Value.int 1));
  ]
;;

let _ =
  run_test_tt_main suite
;;
