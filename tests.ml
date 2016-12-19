open OUnit
open Instr

let ok _ = true

let trace_is li =
  fun conf -> Eval.read_trace conf = li
let has_var x v =
  fun conf -> Eval.(lookup conf.heap conf.env x = v)

let (&&&) p1 p2 conf = (p1 conf) && (p2 conf)

let drop_annots = fst

let no_input = IO.no_input
let input = IO.list_input

let run prog input pred () =
  let final_conf = Eval.run_forever input (drop_annots prog) in
  assert (pred final_conf)

let run_checked prog pred =
  let () = ignore (Scope.infer prog) in
  run prog pred

let exact vars = Some Scope.(Exact (VarSet.of_list vars))
let at_least vars = Some Scope.(At_least (VarSet.of_list vars))

let no_annotations program : Scope.annotated_program =
  (program, Array.map (fun _ -> None) program)

let test_print =
  let open Assembler.OO in
  no_annotations [|
    print (int 1);
    print (int 2);
    stop
  |]

let test_decl_const =
  let open Assembler.OO in
  let x = int_var "x" in
  no_annotations [|
    const x (int 1);
    print x;
    stop;
  |]

let test_mut =
  let open Assembler.OO in
  let x = int_var "x" in
  no_annotations [|
    mut x (int 1);
    print x;
    assign x (int 2);
    print x;
    stop;
  |]

let test_jump =
  let open Assembler.OO in
  let x = int_var "x" in
  no_annotations [|
    mut x (bool true);
    goto "jump";
    assign x (bool false);
    label "jump";
  |]

let test_overloading =
  let open Assembler.OO in
  let b, x, y = bool_var "b", int_var "x", int_var "y" in
  no_annotations [|
    mut b (bool true);
    mut x (int 1);
    const y x;
    goto "jump";
    assign b (bool false);
    label "jump";
    assign x (int 2);
    stop;
  |]

let test_add a b =
  let open Assembler.OO in
  let x, y, z = int_var "x", int_var "y", int_var "z" in
  no_annotations [|
    mut x (int a);
    mut y (int b);
    add z x y;
  |]

let test_eq a b =
  let open Assembler.OO in
  let x, y, z = int_var "x", int_var "y", bool_var "z" in
  no_annotations [|
    mut x (int a);
    mut y (int b);
    eq z x y;
  |]

let test_sum limit_ =
  let open Assembler.OO in
  let ax, i, sum, limit, one =
    bool_var "ax", int_var "i", int_var "sum", int_var "limit", int_var "one" in
  no_annotations [|
    mut i (int 0);
    mut sum (int 0);
    const limit (int limit_);
    const one (int 1);
    label "loop";
    eq ax limit i;
    branch ax "continue" "loop_body";
    label "loop_body";
    add sum sum i;
    add i i one;
    goto "loop";
    label "continue";
    stop;
  |]


let test_broken_scope_1 =
  let open Assembler.OO in
  let x = int_var "x" in
  no_annotations [|
    print x;
  |]

let test_broken_scope_2 =
  let open Assembler.OO in
  let x = int_var "x" in
  no_annotations [|
    goto "l";
    const x (int 0);
    label "l";
    print x;
  |]

let test_broken_scope_3 =
  let open Assembler.OO in
  let x, y = int_var "x", int_var "y" in
  no_annotations [|
    const y (bool false);
    branch y "cont" "next";
    label "next";
    const x (int 0);
    label "cont";
    print x;
  |]

let test_broken_scope_3 =
  let open Assembler.OO in
  let x, y = int_var "x", bool_var "y" in
  no_annotations [|
    const y (bool false);
    branch y "cont" "next";
    label "next";
    const x (int 0);
    label "cont";
    print x;
  |]

let test_broken_scope_4 = Parse.parse_string
"mut x = 0
mut y = 0
{x} mut z = false
z <- (x == y)
"

let test_broken_scope_4_fixed = Parse.parse_string
"mut x = 0
mut y = 0
{x, ...} mut z = false
z <- (x == y)
"

let test_broken_scope_5 = Parse.parse_string
"mut x = 0
mut y = 0
{w, ...} mut z = false
z <- (x == y)
"

let test_scope_1 test_var1 test_var2 =
  let open Assembler.OO in
  let a, b, c, t = int_var "a", int_var "b", int_var "c", bool_var "t" in
  no_annotations [|
    const t (bool false);
    branch t "a" "b";
    label "a";
    const a (int 0);
    const c (int 0);
    goto "cont";
    label "b";
    const b (int 0);
    const c (int 0);
    goto "cont";
    label "cont";
    add c (int_var test_var1) (int_var test_var2);
  |]

let test_read_print =
  let open Assembler.OO in
  let n, b = int_var "n", bool_var "b" in
  no_annotations [|
    mut n (int 0);
    mut b (bool true);
    read b;
    read n;
    print n;
    print b;
  |]

let infer_broken_scope program missing_vars = function() ->
     let test = function() -> ignore (Scope.infer program) in
     let expected = Scope.(UndefinedVariable (VarSet.of_list missing_vars)) in
     assert_raises expected test

let test_parse_disasm_file file = function() ->
  let prog1 = Parse.parse_file file in
  let disasm1 = Disasm.disassemble_annotated prog1 in
  let prog2 = Parse.parse_string disasm1 in
  let disasm2 = Disasm.disassemble_annotated prog2 in
  assert_equal disasm1 disasm2

let test_parse_disasm str = function() ->
  let prog1 = Parse.parse_string str in
  let disasm1 = Disasm.disassemble_annotated prog1 in
  let prog2 = Parse.parse_string disasm1 in
  let disasm2 = Disasm.disassemble_annotated prog2 in
  assert_equal disasm1 disasm2

let test_disasm_parse prog = function() ->
  let disasm1 = Disasm.disassemble_annotated prog in
  let prog2 = Parse.parse_string disasm1 in
  assert_equal prog prog2

let test_branch = Parse.parse_string
"mut x = 9
 mut y = 10
 mut r = 1
 branch (x == y) l1 l2
l1:
 r <- 2
 goto c
l2:
 r <- 3
 goto c
c:
 print r
"

let test_branch_pruned = " mut x = 9
 mut y = 10
 mut r = 1
 invalidate (x == y) %deopt_l2 [r, x, y]
 r <- 2
 print r
 stop
 #Landing pad for deopt %deopt_l2
%deopt_l2:
 r <- 3
 print r
 stop
"

let test_double_loop = Parse.parse_string
"mut i = 0
 mut sum = 0
 const limit = 4
 const one = 1
loop1:
  branch (i != limit) loop_body1 continue
loop_body1:
   mut i2 = 0
   mut sum2 = 0
loop2:
    branch (i2 != limit) loop_body2 continue2
loop_body2:
     print i2
     sum2 <- (sum + i2)
     i2 <- (i2 + one)
    goto loop2
continue2:
   sum <- (sum + sum2)
   i <- (i + one)
 goto loop1
continue:
 print sum
"

let test_branch_pruning_exp prog expected =
  let scope = Scope.infer prog in
  let instrs = (drop_annots prog) in
  let prog2 = Transform.branch_prune (instrs, scope) in
  assert_equal (Disasm.disassemble prog2) expected

let test_branch_pruning prog deopt =
  let open Eval in
  let scope = Scope.infer prog in
  let instrs = (drop_annots prog) in
  let prog2 = Transform.branch_prune (instrs, scope) in
  let res1 = Eval.run_forever no_input instrs in
  let res2 = Eval.run_forever no_input prog2 in
  assert_equal res1.trace res2.trace;
  assert_equal res2.deopt (Some deopt)

let assert_equal_sorted li1 li2 =
  assert_equal (List.sort compare li1) (List.sort compare li2)

let test_pred = fst (Parse.parse_string
"l1:
  goto l2
 l3:
  branch x l1 l2
 l2:
  branch x l1 l3
  stop
  goto l1
")
let do_test_pred = function () ->
  let pred = Analysis.predecessors test_pred in
  let pred pc = pred.(pc) in
  assert_equal_sorted (pred 0) [3; 5; 7];
  assert_equal_sorted (pred 1) [0];
  assert_equal_sorted (pred 2) [5];
  assert_equal_sorted (pred 3) [2];
  assert_equal_sorted (pred 4) [1; 3];
  assert_equal_sorted (pred 5) [4];
  assert_equal_sorted (pred 6) [];
  assert_equal_sorted (pred 7) []

let suite =
  let open Assembler in
  "suite">:::
  ["mut">:: run_checked test_mut no_input
     (has_var "x" (Value.int 2)
      &&& (trace_is Value.[int 1; int 2]));
   "decl_const">:: run_checked test_decl_const no_input
     (has_var "x" (Value.int 1));
   "print">:: run_checked test_print no_input
     (trace_is Value.[int 1; int 2]);
   "jump">:: run_checked test_jump no_input
     (has_var "x" (Value.bool true));
   "jump (oo)" >:: run_checked test_overloading no_input
     (has_var "b" (Value.bool true)
      &&& has_var "x" (Value.int 2)
      &&& has_var "y" (Value.int 1));
   "add">:: run_checked (test_add 1 2) no_input
     (has_var "z" (Value.int 3));
   "add2">:: run_checked (test_add 2 1) no_input
     (has_var "z" (Value.int 3));
   "eq">:: run_checked (test_eq 1 2) no_input
     (has_var "z" (Value.bool false));
   "neq">:: run_checked (test_eq 1 1) no_input
     (has_var "z" (Value.bool true));
   "loops">:: run_checked (test_sum 5) no_input
     (has_var "sum" (Value.int 10));
   "read">:: run_checked test_read_print (input [Value.bool false; Value.int 1])
     (trace_is [Value.int 1; Value.bool false]);
   "scope1">:: infer_broken_scope test_broken_scope_1 ["x"];
   "scope2">:: infer_broken_scope test_broken_scope_2 ["x"];
   "scope3">:: infer_broken_scope test_broken_scope_3 ["x"];
   "scope3run">:: run test_broken_scope_3 no_input
     (has_var "x" (Value.int 0));
   "scope4">:: infer_broken_scope test_broken_scope_4 ["y"];
   "scope4fixed">:: run_checked test_broken_scope_4_fixed no_input ok;
   "scope5">:: infer_broken_scope test_broken_scope_5 ["w"];
   "scope1ok">:: run_checked (test_scope_1 "c" "c") no_input
     (has_var "c" (Value.int 0));
   "scope1broken">:: infer_broken_scope (test_scope_1 "a" "c") ["a"];
   "scope1broken2">:: infer_broken_scope (test_scope_1 "a" "b") ["b"; "a"];
   "parser">:: test_parse_disasm ("stop\n");
   "parser1">:: test_parse_disasm ("const x = 3\nprint x\nstop\n");
   "parser2">:: test_parse_disasm ("goto l\nx <- 3\nl:\n");
   "parser3">:: test_parse_disasm ("const x = (y + x)\n");
   "parser4">:: test_parse_disasm ("x <- (x == y)\n");
   "parser5">:: test_parse_disasm ("# asdfasdf\n");
   "parser5b">:: test_parse_disasm ("invalidate (x == y) l [x, y, z]\nl:\n");
   "parser6">:: test_parse_disasm ("branch (x == y) as fd\n");
   "parser7">:: test_parse_disasm ("const x = (y + x)\n x <- (x == y)\n# asdfasdf\nbranch (x == y) as fd\n");
   "parser8">:: test_parse_disasm_file "examples/test.sou";
   "disasm1">:: test_disasm_parse (test_sum 10);
   "disasm2">:: test_disasm_parse (test_add 1 0);
   "disasm_scope1">:: test_disasm_parse test_broken_scope_4;
   "disasm_scope2">:: test_disasm_parse test_broken_scope_4_fixed;
   "disasm_scope3">:: test_disasm_parse test_broken_scope_5;
   "parser_scope1">:: test_parse_disasm "{a, b} print x\n{a,x,...} #asdf\n";
   "branch_pruning">:: (fun () -> test_branch_pruning_exp test_branch test_branch_pruned);
   "predecessors">:: do_test_pred;
   "branch_pruning_eval">:: (fun () -> test_branch_pruning test_branch "%deopt_l2");
   "branch_pruning_eval2">:: (fun () -> test_branch_pruning (test_sum 10) "%deopt_loop_body");
   "branch_pruning_eval3">:: (fun () -> test_branch_pruning test_double_loop "%deopt_continue2");
   ]
;;

let _ =
  run_test_tt_main suite;
;;
