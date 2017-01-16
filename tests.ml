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
  let rc (prog, pred) =
    let () = ignore (Scope.infer prog) in
    run prog pred in
  rc (prog, pred)

let exact vars = Some Scope.(Exact (VarSet.of_list vars))
let at_least vars = Some Scope.(At_least (VarSet.of_list vars))

let no_annotations program : annotated_program =
  (program, Array.map (fun _ -> None) program)

let parse_test str =
  try Parse.parse_string str
  with Parse.Error error ->
    Parse.report_error error;
    exit 2


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

let test_eq a b = parse_test (
" mut x = "^ string_of_int a ^"
  mut y = "^ string_of_int b ^"
  const z = (x==y)
")

let test_sum limit_ = parse_test (
" mut i = 0
  mut sum = 0
  const limit = "^string_of_int limit_^"
loop:
  const ax = (i==limit)
  branch ax continue loop_body
loop_body:
  sum <- (sum+i)
  i <- (i+1)
  goto loop
continue:
  stop
")

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

let test_broken_scope_4 = parse_test
"mut x = 0
mut y = 0
{x} mut z = false
z <- (x == y)
"

let test_broken_scope_4_fixed = parse_test
"mut x = 0
mut y = 0
{x, ...} mut z = false
z <- (x == y)
"

let test_broken_scope_5 = parse_test
"mut x = 0
mut y = 0
{w, ...} mut z = false
z <- (x == y)
"

let test_scope_1 test_var1 test_var2 = parse_test (
" mut t = false
  branch t a b
a:
  const a = 0
  const c = 0
  goto cont
b:
  const b = 0
  const c = 0
cont:
  const res = (" ^ test_var1 ^ " + " ^ test_var2 ^ ")
")

let test_read_print = parse_test
"   mut n
    mut b
    read b
    read n
    print n
    print b
"
let test_read_print_err = parse_test
"   mut n
    read b
    read n
    print n
    print b
"
let test_read_print_err_2 = parse_test
"   mut n
    mut b
    read b
    print n
    print b
"

let infer_broken_scope program missing_vars = function() ->
     let test = function() -> ignore (Scope.infer program) in
     let expected = Scope.(UndeclaredVariable (VarSet.of_list missing_vars)) in
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

let test_branch = parse_test
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
 invalidate (x == y) deopt_l2 []
 r <- 2
 print r
 stop
 #Landing pad for deopt_l2
deopt_l2:
 mut r
 mut x
 mut y
 r <- 3
 print r
 stop
"

let test_double_loop = parse_test
"mut i
 i <- 0
 mut sum = 0
 const limit = 4
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
     i2 <- (i2 + 1)
    goto loop2
continue2:
   sum <- (sum + sum2)
   i <- (i + 1)
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

let test_pred = fst (parse_test
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

let test_df = fst (parse_test
"mut a = 1
 mut b = 2
 mut d = (a+b)
 # space
 b <- 3
 mut z = (a+b)
l:
 mut y = (a+b)
 b <- 4
 branch b l l2
 # gap
l2:
 mut y = (y+b)
 branch b l l3
l3:
")

let do_test_liveness = function () ->
  let open Analysis in
  let live = live test_df in
  assert_equal_sorted (live 0) ["a"];
  assert_equal_sorted (live 1) ["a";"b"];
  assert_equal_sorted (live 2) ["a"];
  assert_equal_sorted (live 3) ["a"];
  assert_equal_sorted (live 4) ["a";"b"];
  assert_equal_sorted (live 5) ["a";"b"];
  assert_equal_sorted (live 6) ["a";"b"];
  assert_equal_sorted (live 7)  ["a";"y"];
  assert_equal_sorted (live 8)  ["a";"b";"y"];
  assert_equal_sorted (live 9)  ["a";"b";"y"];
  assert_equal_sorted (live 11) ["a";"b";"y"];
  assert_equal_sorted (live 12) ["a";"b"];
  assert_equal_sorted (live 13) ["a";"b"];
  assert_equal_sorted (live 0) ["a"]


let do_test_used = function () ->
  let open Analysis in
  let used = used test_df in
  assert_equal_sorted (InstrSet.elements (used 0)) [2;5;7];
  assert_equal_sorted (InstrSet.elements (used 1)) [2];
  assert_equal_sorted (InstrSet.elements (used 2)) [];
  assert_equal_sorted (InstrSet.elements (used 4)) [5;7];
  assert_equal_sorted (InstrSet.elements (used 5)) [];
  assert_equal_sorted (InstrSet.elements (used 7)) [12];
  assert_equal_sorted (InstrSet.elements (used 8)) [7;9;12;13];
  assert_equal_sorted (InstrSet.elements (used 9)) [];
  assert_equal_sorted (InstrSet.elements (used 11)) [];
  assert_equal_sorted (InstrSet.elements (used 12)) [];
  assert_equal_sorted (InstrSet.elements (used 13)) [];
  assert_equal_sorted (InstrSet.elements (used 6)) []


let do_test_reaching = function () ->
  let open Analysis in
  let reaching = reaching test_df in
  assert_equal_sorted (InstrSet.elements (reaching 0)) [];
  assert_equal_sorted (InstrSet.elements (reaching 1)) [];
  assert_equal_sorted (InstrSet.elements (reaching 2)) [0;1];
  assert_equal_sorted (InstrSet.elements (reaching 5)) [0;4];
  assert_equal_sorted (InstrSet.elements (reaching 7)) [8;0;4];
  assert_equal_sorted (InstrSet.elements (reaching 12)) [8;7];
  assert_equal_sorted (InstrSet.elements (reaching 0)) []

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
   "mut_undeclared">:: (fun () -> assert_raises (Eval.Unbound_variable "b")
                           (run test_read_print_err (input [Value.bool false; Value.int 1]) ok));
   "mut_undeclared2">:: (fun () -> assert_raises (Scope.UndeclaredVariable (VarSet.singleton "b"))
                           (fun() -> run_checked test_read_print_err (input [Value.bool false; Value.int 1]) ok ()));
   "mut_undefined">:: (fun () -> assert_raises (Eval.Undefined_variable "n")
                           (run test_read_print_err_2 (input [Value.bool false; Value.int 1]) ok));
   "mut_undefined2">:: (fun () -> assert_raises (Scope.UninitializedVariable (VarSet.singleton "n"))
                           (fun() -> run_checked test_read_print_err_2 (input [Value.bool false; Value.int 1]) ok ()));
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
   "parser8">:: test_parse_disasm_file "examples/sum.sou";
   "disasm1">:: test_disasm_parse (test_sum 10);
   "disasm2">:: test_disasm_parse (test_add 1 0);
   "disasm_scope1">:: test_disasm_parse test_broken_scope_4;
   "disasm_scope2">:: test_disasm_parse test_broken_scope_4_fixed;
   "disasm_scope3">:: test_disasm_parse test_broken_scope_5;
   "parser_scope1">:: test_parse_disasm "{a, b} print x\n{a,x,...} #asdf\n";
   "branch_pruning">:: (fun () -> test_branch_pruning_exp test_branch test_branch_pruned);
   "predecessors">:: do_test_pred;
   "branch_pruning_eval">:: (fun () -> test_branch_pruning test_branch "deopt_l2");
   "branch_pruning_eval2">:: (fun () -> test_branch_pruning (test_sum 10) "deopt_loop_body");
   "branch_pruning_eval3">:: (fun () -> test_branch_pruning test_double_loop "deopt_continue2");
   "reaching">:: do_test_reaching;
   "used">:: do_test_used;
   "liveness">:: do_test_liveness;
   ]
;;

let _ =
  run_test_tt_main suite;
;;
