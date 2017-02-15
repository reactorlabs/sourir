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

let check annotated_program =
  let check_segment (name, (instrs, annot)) =
    Scope.check (Scope.infer instrs) annot in
  List.iter check_segment annotated_program;
  Scope.drop_annots annotated_program

let run_checked prog input pred () =
  let final_conf = Eval.run_forever input prog in
  assert (pred final_conf)

let run prog input pred () =
  run_checked (Scope.drop_annots prog) input pred ()

let exact vars = Some Scope.(Exact (VarSet.of_list vars))
let at_least vars = Some Scope.(At_least (VarSet.of_list vars))

let parse_annotated str : Scope.annotated_program =
  try Parse.parse_string ("segment main\n" ^ str)
  with Parse.Error error ->
    Parse.report_error error;
    exit 2

let parse_and_check str : Instr.program =
  check (parse_annotated str)

let parse_no_check str = Scope.drop_annots (parse_annotated str)

let check_and_run annotated_program input pred =
  run_checked (check annotated_program) input pred

let parse_test = parse_and_check

let test_print = parse_test
" print 1
  print 2
  stop
"

let test_decl_const = parse_test
" const x  = 1
  print x
  stop
"

let test_mut = parse_test
" mut x = 1
  print x
  x <- 2
  print x
  stop
"

let test_jump = parse_test
" mut x = true
  goto jmp
  x <- false
 jmp:
"

let test_overloading = parse_test
" mut b = true
  mut x = 1
  const y = x
  goto jump
  b <- false
 jump:
  x <- 2
  stop
"

let test_add a b = parse_test (
" mut x = "^a^"
  mut y = "^b^"
  mut z = (x + y)
")

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
  drop ax
  sum <- (sum+i)
  i <- (i+1)
  goto loop
continue:
  drop ax
  stop
")

let test_broken_scope_1 = parse_annotated
" print x
"

let test_broken_scope_2 = parse_annotated
" goto l
  const x = 0
 l:
  print x
"

let test_broken_scope_3 = parse_annotated
" const y = false
  branch y cont next
 next:
  const x = 0
  drop x
 cont:
  print x
"

let test_broken_scope_4 = parse_annotated
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

let test_broken_scope_5 = parse_annotated
"mut x = 0
mut y = 0
{w, ...} mut z = false
z <- (x == y)
"

let test_scope_1 test_var1 test_var2 = parse_annotated (
" mut t = false
  branch t a b
a:
  const a = 0
  const c = 0
  drop a
  goto cont
b:
  const b = 0
  const c = 0
  drop b
cont:
  const res = (" ^ test_var1 ^ " + " ^ test_var2 ^ ")
")

let test_read_print = parse_test
"   mut n
    mut b
    read b
    read n
    print n
    drop n
    print b
    drop b
"
let test_read_print_err = parse_annotated
"   mut n
    read b
    read n
    print n
    print b
"
let test_read_print_err_2 = parse_annotated
"   mut n
    mut b
    read b
    print n
    print b
"
let test_read_print_err_3 = parse_annotated
"   mut n
    mut b
    read b
    read n
    drop b
    print n
    print b
"
let test_read_print_err_4 = parse_annotated
"   mut n
    mut b
    read b
    read n
    clear b
    print n
    print b
"

let do_test_scope_uninitialized = function () ->
  assert_raises (Scope.UninitializedVariable (VarSet.singleton "x", 2)) (fun () -> ignore (parse_test "
     mut x = 1
    loop:
     print x
     clear x
     goto loop
    "));
  assert_raises (Scope.UninitializedVariable (VarSet.singleton "x", 2)) (fun () -> ignore (parse_test "
     mut x = 1
    loop:
     print x
     branch (x==1) clearit loop
    clearit:
     clear x
     goto loop
    "));
  (* Positive example: even though one branch cleares x it is restored at the end *)
  ignore (parse_test "
     mut x = 1
    loop:
     print x
     branch (x==1) clearit skip
    clearit:
     clear x
    skip:
     x <- 7
     goto loop
    ")




let undeclared missing_vars pos =
  Scope.UndeclaredVariable (VarSet.of_list missing_vars, pos)

let extraneous extra_vars pos =
  Scope.ExtraneousVariable (VarSet.of_list extra_vars, pos)

let infer_broken_scope program exn = function() ->
  let (instrs, annot) = List.assoc "main" program in
  let test () = Scope.check (Scope.infer instrs) annot in
  assert_raises exn test

let test_parse_disasm_file file = function() ->
  let prog1 = Scope.drop_annots (Parse.parse_file file) in
  let disasm1 = Disasm.disassemble prog1 in
  let prog2 = Scope.drop_annots (Parse.parse_string disasm1) in
  let disasm2 = Disasm.disassemble prog2 in
  assert_equal disasm1 disasm2

let test_parse_disasm str = function() ->
  let prog1 = Scope.drop_annots (Parse.parse_string str) in
  let disasm1 = Disasm.disassemble prog1 in
  let prog2 = Scope.drop_annots (Parse.parse_string disasm1) in
  let disasm2 = Disasm.disassemble prog2 in
  assert_equal disasm1 disasm2

let test_disasm_parse prog = function() ->
  let disasm1 = Disasm.disassemble prog in
  let prog2 = Scope.drop_annots (Parse.parse_string disasm1) in
  let disasm2 = Disasm.disassemble prog2 in
  assert_equal disasm1 disasm2

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
 clear r
"

let test_branch_pruned =
"segment main
 mut x = 9
 mut y = 10
 mut r = 1
 osr (x == y) main_1 l1 [mut r, mut x, mut y]
 r <- 3
 print r
 clear r
segment main_1
 mut x = 9
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
 clear r
"

let test_double_loop = parse_test
"{} mut i
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
   drop i2
   drop sum2
   i <- (i + 1)
 goto loop1
continue:
 print sum
"

let test_branch_pruning_exp prog expected =
  let prog2 = Transform.branch_prune prog in
  assert_equal (Disasm.disassemble prog2) expected

let test_branch_pruning prog deopt =
  let open Eval in
  let prog2 = Transform.branch_prune prog in
  let res1 = Eval.run_forever no_input prog in
  let res2 = Eval.run_forever no_input prog2 in
  assert_equal res1.trace res2.trace;
  assert_equal res2.deopt deopt

let assert_equal_sorted li1 li2 =
  assert_equal (List.sort compare li1) (List.sort compare li2)

let test_pred = parse_no_check
"l1:
  goto l2
 l3:
  branch x l1 l2
 l2:
  branch x l1 l3
  stop
  goto l1
"

let do_test_pred = function () ->
  let pred = Analysis.predecessors (List.assoc "main" test_pred) in
  let pred pc = pred.(pc) in
  assert_equal_sorted (pred 0) [3; 5; 7];
  assert_equal_sorted (pred 1) [0];
  assert_equal_sorted (pred 2) [5];
  assert_equal_sorted (pred 3) [2];
  assert_equal_sorted (pred 4) [1; 3];
  assert_equal_sorted (pred 5) [4];
  assert_equal_sorted (pred 6) [];
  assert_equal_sorted (pred 7) []

let test_df = parse_no_check
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
"

let do_test_dom1 = function () ->
  let open Cfg in
  let instrs = List.assoc "main" test_df in
  let cfg = Cfg.of_program instrs in
  let doms = dominators (test_df, cfg) in
  let expected = [| []; [0]; [0;1]; [0;1;2]; |] in
  let got = Array.map (fun s ->
    List.map (fun n -> n.id) (BasicBlockSet.elements s)) doms in
  assert_equal got expected;
  let c1 = common_dominator (test_df, cfg, doms) [8; 14] in
  let c2 = common_dominator (test_df, cfg, doms) [8; 13] in
  let c3 = common_dominator (test_df, cfg, doms) [12; 13] in
  assert_equal c1.id 1;
  assert_equal c2.id 1;
  assert_equal c3.id 2

(* compare a CFG against a blueprint. The blueprint uses
 * array indices as successors instead of references to the
 * successor BB.
 * This is required since otherwise it is (i) annoying to
 * construct the expected CFG and (ii) assert_equals diverges
 * on circular CFGs *)
type bb_blueprint = {entry : pc; exit : pc; succ : int list}
let compare_cfg (cfg : Cfg.cfg) (cfg_blueprint : bb_blueprint array) =
  let open Cfg in
  assert_equal (Array.length cfg) (Array.length cfg_blueprint);
  Array.iteri (fun i (expected : bb_blueprint) ->
      let node = cfg.(i) in
      assert_equal expected.entry node.entry;
      assert_equal expected.exit node.exit;
      let succ = List.map (fun n -> n.id) node.succ in
      assert_equal expected.succ succ
    ) cfg_blueprint

let do_test_cfg = function () ->
  let open Cfg in
  let instrs = List.assoc "main" test_df in
  let cfg = Cfg.of_program instrs in
  let expected = [|
      {entry=0; exit=5; succ=[1]};
      {entry=6; exit=9; succ=[1;2]};
      {entry=11; exit=13; succ=[1;3]};
      {entry=14; exit=14; succ=[]} |] in
  compare_cfg cfg expected

let do_test_liveness = function () ->
  let seg = List.assoc "main" test_df in
  let open Analysis in
  let live = live seg in
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
  let seg = List.assoc "main" test_df in
  let open Analysis in
  let used = used seg in
  assert_equal_sorted (PcSet.elements (used 0)) [2;5;7];
  assert_equal_sorted (PcSet.elements (used 1)) [2];
  assert_equal_sorted (PcSet.elements (used 2)) [];
  assert_equal_sorted (PcSet.elements (used 4)) [5;7];
  assert_equal_sorted (PcSet.elements (used 5)) [];
  assert_equal_sorted (PcSet.elements (used 7)) [12];
  assert_equal_sorted (PcSet.elements (used 8)) [7;9;12;13];
  assert_equal_sorted (PcSet.elements (used 9)) [];
  assert_equal_sorted (PcSet.elements (used 11)) [];
  assert_equal_sorted (PcSet.elements (used 12)) [];
  assert_equal_sorted (PcSet.elements (used 13)) [];
  assert_equal_sorted (PcSet.elements (used 6)) []


let do_test_reaching = function () ->
  let seg = List.assoc "main" test_df in
  let open Analysis in
  let reaching = reaching seg in
  assert_equal_sorted (PcSet.elements (reaching 0)) [];
  assert_equal_sorted (PcSet.elements (reaching 1)) [];
  assert_equal_sorted (PcSet.elements (reaching 2)) [0;1];
  assert_equal_sorted (PcSet.elements (reaching 5)) [0;4];
  assert_equal_sorted (PcSet.elements (reaching 7)) [8;0;4];
  assert_equal_sorted (PcSet.elements (reaching 12)) [8;7];
  assert_equal_sorted (PcSet.elements (reaching 0)) []

let test_df2 = parse_no_check
" goto jmp
start:
  mut i = 1
  mut c = 0
  mut v = 123
  mut x = 0
  loop:
    branch (i==10) loop_end loop_begin
  loop_begin:
    mut w = 3
    branch (c==2) tr fs
    tr:
      w <- 3
      goto ct
    fs:
      branch (c==4) tr2 fs2
      tr2:
        stop
    fs2:
      w <- 4
      goto ct
  ct:
    x <- w
    v <- (c+1)
    i <- (i+v)
    goto loop
loop_end:
  print i
  print x
  # bla
  goto end
jmp:
  branch true start end
end:
"

let do_test_dom prog = function () ->
  let cfg = Cfg.of_program prog in
  let doms = Cfg.dominators (prog, cfg) in
  let c = Cfg.common_dominator (test_df2, cfg, doms) [12; 19] in
  let expected = Cfg.node_at cfg 9 in
  let open Cfg in
  assert_equal c.id expected.id

let suite =
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
   "add">:: run_checked (test_add "1" "2") no_input
     (has_var "z" (Value.int 3));
   "add2">:: run_checked (test_add "2" "1") no_input
     (has_var "z" (Value.int 3));
   "eq">:: run_checked (test_eq 1 2) no_input
     (has_var "z" (Value.bool false));
   "neq">:: run_checked (test_eq 1 1) no_input
     (has_var "z" (Value.bool true));
   "loops">:: run_checked (test_sum 5) no_input
     (has_var "sum" (Value.int 10));
   "read">:: run_checked test_read_print (input [Value.bool false; Value.int 1])
     (trace_is [Value.int 1; Value.bool false]);
   "mut_undeclared">::
   (fun () -> assert_raises (Eval.Unbound_variable "b")
       (run test_read_print_err
          (input [Value.bool false; Value.int 1]) ok));
   "mut_undeclared2">::
   (fun () -> assert_raises (Scope.UndeclaredVariable (VarSet.singleton "b", 1))
       (fun() -> run_checked (check test_read_print_err)
           (input [Value.bool false; Value.int 1]) ok ()));
   "mut_undeclared3">::
   (fun () -> assert_raises (Scope.UndeclaredVariable (VarSet.singleton "b", 6))
       (fun() -> run_checked (check test_read_print_err_3)
           (input [Value.bool false; Value.int 1]) ok ()));
   "mut_undefined">::
   (fun () -> assert_raises (Eval.Undefined_variable "n")
       (run test_read_print_err_2
          (input [Value.bool false; Value.int 1]) ok));
   "mut_undefined2">::
   (fun () -> assert_raises (Scope.UninitializedVariable (VarSet.singleton "n", 3))
       (fun() -> run_checked (check test_read_print_err_2)
           (input [Value.bool false; Value.int 1]) ok ()));
   "mut_undefined3">::
   (fun () -> assert_raises (Scope.UninitializedVariable (VarSet.singleton "b", 6))
       (fun() -> run_checked (check test_read_print_err_4)
           (input [Value.bool false; Value.int 1]) ok ()));
   "scope1">:: infer_broken_scope test_broken_scope_1 (undeclared ["x"] 0);
   "scope2">:: infer_broken_scope test_broken_scope_2 (undeclared ["x"] 3);
   "scope3">:: infer_broken_scope test_broken_scope_3 (undeclared ["x"] 6);
   "scope4">:: infer_broken_scope test_broken_scope_4 (extraneous ["y"] 2);
   "scope4fixed">:: run_checked test_broken_scope_4_fixed no_input ok;
   "scope5">:: infer_broken_scope test_broken_scope_5 (undeclared ["w"] 2);
   "scope1ok">:: check_and_run (test_scope_1 "c" "c") no_input
     (has_var "c" (Value.int 0));
   "scope1broken">:: infer_broken_scope
     (test_scope_1 "a" "c") (undeclared ["a"] 12);
   "scope1broken2">:: infer_broken_scope
     (test_scope_1 "a" "b") (undeclared ["b"; "a"] 12);
   "scope_uninitialized">:: do_test_scope_uninitialized;
   "parser">:: test_parse_disasm ("segment main\nstop\n");
   "parser1">:: test_parse_disasm ("segment asdf\nconst x = 3\nprint x\nstop\n");
   "parser2">:: test_parse_disasm ("segment asdf\ngoto l\nx <- 3\nl:\n");
   "parser3">:: test_parse_disasm ("segment asdf\nconst x = (y + x)\n");
   "parser4">:: test_parse_disasm ("segment asdf\nx <- (x == y)\n");
   "parser5">:: test_parse_disasm ("segment asdf\n# asdfasdf\n");
   "parser5b">:: test_parse_disasm ("segment as\nosr (x == y) v l [const x = x, mut y = x, mut v, const x = (1+2)]\nl:\n");
   "parser6">:: test_parse_disasm ("segment s\nbranch (x == y) as fd\n");
   "parser7">:: test_parse_disasm ("segment x\nconst x = (y + x)\n x <- (x == y)\n# asdfasdf\nbranch (x == y) as fd\n");
   "parser8">:: test_parse_disasm_file "examples/sum.sou";
   "disasm1">:: test_disasm_parse (test_sum 10);
   "disasm2">:: test_disasm_parse (test_add "1" "0");
   "disasm_scope1">:: test_disasm_parse
     (Scope.drop_annots test_broken_scope_4);
   "disasm_scope2">:: test_disasm_parse
     test_broken_scope_4_fixed;
   "disasm_scope3">:: test_disasm_parse
     (Scope.drop_annots test_broken_scope_5);
   "parser_scope1">:: test_parse_disasm "segment x\n{a, b} print x\n{a,x,...} #asdf\n";
   "branch_pruning">:: (fun () -> test_branch_pruning_exp test_branch test_branch_pruned);
   "predecessors">:: do_test_pred;
   "branch_pruning_eval">:: (fun () -> test_branch_pruning test_branch None);
   "branch_pruning_eval2">:: (fun () -> test_branch_pruning (test_sum 10) (Some "continue"));
   "branch_pruning_eval3">:: (fun () -> test_branch_pruning test_double_loop (Some "loop_body1"));
   "reaching">:: do_test_reaching;
   "used">:: do_test_used;
   "liveness">:: do_test_liveness;
   "cfg">:: do_test_cfg;
   "dom">:: do_test_dom1;
   "dom2">:: do_test_dom (List.assoc "main" test_df2);
   ]
;;

let () =
  let test_result = run_test_tt_main suite in
  let is_success = function[@warning "-4"]
    | RSuccess _ -> true
    | _ -> false in
  if not (List.for_all is_success test_result) then exit 1;;
