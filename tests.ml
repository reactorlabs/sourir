open OUnit
open Instr

let ok _ = true

let trace_is li =
  fun conf -> Eval.read_trace conf = li
let has_var x v =
  fun conf -> Eval.(lookup conf.heap conf.env x = v)
let returns n =
  fun conf -> Eval.(conf.status = Result n)

let (&&&) p1 p2 conf = (p1 conf) && (p2 conf)

let drop_annots = fst

let no_input = IO.no_input
let input = IO.list_input

let run prog input pred () =
  Check.well_formed prog;
  Scope.check_program prog;
  let final_conf = Eval.run_forever input prog in
  assert (pred final_conf)

let run_unchecked prog input pred () =
  let final_conf = Eval.run_forever input prog in
  assert (pred final_conf)

let parse str : program =
  try Parse.program_of_string str
  with Parse.Error error as exn ->
    Parse.report_error error;
    raise exn

let test_print = parse
" print 1
  print 2
  stop 0
"

let test_decl_var = parse
" var x = 1
  print x
  stop 0
"

let test_incr_var = parse
" var x = 1
  x <- (x + 1)
  print x
  stop 0
"

let test_var = parse
" var x = 1
  print x
  x <- 2
  print x
  stop 0
"

let test_jump = parse
" var x = true
  goto jmp
  x <- false
  goto jmp
 jmp:
"

let test_overloading = parse
" var b = true
  var x = 1
  var y = x
  goto jump
  b <- false
  goto jump
 jump:
  x <- 2
  stop 0
"

let test_neg a = parse (
" var x = "^ string_of_int a ^"
  var y = (-x)
")

let test_add a b = parse (
" var x = "^a^"
  var y = "^b^"
  var z = (x + y)
")

let test_sub a b = parse (
" var x = "^a^"
  var y = "^b^"
  var z = (x - y)
")

let test_mult a b = parse (
" var x = "^a^"
  var y = "^b^"
  var z = (x * y)
")

let test_div a b = parse (
" var x = "^a^"
  var y = "^b^"
  var z = (x / y)
")

let test_mod a b = parse (
" var x = "^a^"
  var y = "^b^"
  var z = (x % y)
")

let test_eq a b = parse (
" var x = "^ string_of_int a ^"
  var y = "^ string_of_int b ^"
  var z = (x==y)
")

let test_neq a b = parse (
" var x = "^ string_of_int a ^"
  var y = "^ string_of_int b ^"
  var z = (x!=y)
")

let test_lt a b = parse (
" var x = "^ string_of_int a ^"
  var y = "^ string_of_int b ^"
  var z = (x<y)
")

let test_lte a b = parse (
" var x = "^ string_of_int a ^"
  var y = "^ string_of_int b ^"
  var z = (x<=y)
")

let test_gt a b = parse (
" var x = "^ string_of_int a ^"
  var y = "^ string_of_int b ^"
  var z = (x>y)
")

let test_gte a b = parse (
" var x = "^ string_of_int a ^"
  var y = "^ string_of_int b ^"
  var z = (x>=y)
")

let test_not a = parse (
" var x = "^ string_of_bool a ^"
  var y = (!x)
")

let test_and a b = parse (
" var x = "^ string_of_bool a^"
  var y = "^ string_of_bool b^"
  var z = (x && y)
")

let test_or a b = parse (
" var x = "^ string_of_bool a^"
  var y = "^ string_of_bool b^"
  var z = (x || y)
")

let test_sum limit_ = parse (
" var i = 0
  var sum = 0
  var limit = "^string_of_int limit_^"
  goto loop
loop:
  var ax = (i==limit)
  branch ax $continue $loop_body
$loop_body:
  drop ax
  sum <- (sum+i)
  i <- (i+1)
  goto loop
$continue:
  drop ax
  stop 0
")

let test_broken_scope_1 = parse
" print x
"

let test_broken_scope_2 = parse
" goto l
  var x = 0
 l:
  print x
"

let test_broken_scope_3 = parse
" var y = false
  branch y $cont $next
 $next:
  var x = 0
  drop x
  goto ft
 $cont:
  goto ft
 ft:
  print x
"

let test_broken_scope_4 = parse
"var x = 0
var y = 0
{x} var z = false
z <- (x == y)
"

let test_broken_scope_4_fixed = parse
"var x = 0
var y = 0
{x, ...} var z = false
z <- (x == y)
"

let test_broken_scope_5 = parse
"var x = 0
var y = 0
{w, ...} var z = false
z <- (x == y)
"

let test_scope_1 test_var1 test_var2 = parse (
" var t = false
  var c
  branch t $a $b
$a:
  var a = 0
  c <- 0
  drop a
  goto cont
$b:
  var b = 0
  c <- 0
  drop b
  goto cont
cont:
  var res = (" ^ test_var1 ^ " + " ^ test_var2 ^ ")
")

let test_read_print = parse
"   var n
    var b
    read b
    read n
    print n
    drop n
    print b
    drop b
"
let test_read_print_err = parse
"   var n
    read b
    read n
    print n
    print b
"
let test_read_print_err_2 = parse
"   var n
    var b
    read b
    print n
    print b
"
let test_read_print_err_3 = parse
"   var n
    var b
    read b
    read n
    drop b
    print n
    print b
"
let test_read_print_err_4 = parse
"   var n
    var b
    read b
    read n
    b <- nil
    print n
    print b
"

let undeclared missing_vars pos =
  Scope.ScopeExceptionAt("main", "anon", Scope.UndeclaredVariable (VarSet.of_list missing_vars, pos))

let extraneous extra_vars pos =
  Scope.ScopeExceptionAt("main", "anon", Scope.ExtraneousVariable (VarSet.of_list extra_vars, pos))

let infer_broken_scope program exn = function() ->
  let test () = Scope.check_program program in
  assert_raises exn test

let assert_equal_string s1 s2 = assert_equal ~printer:(fun x -> x) s1 s2

let test_parse_disasm_file file = function() ->
  let prog1 = Parse.program_of_file file in
  let disasm1 = Disasm.disassemble_s prog1 in
  let prog2 = Parse.program_of_string disasm1 in
  let disasm2 = Disasm.disassemble_s prog2 in
  assert_equal_string disasm1 disasm2

let test_parse_disasm str = function() ->
  let prog1 = Parse.program_of_string str in
  let disasm1 = Disasm.disassemble_s prog1 in
  let prog2 = Parse.program_of_string disasm1 in
  let disasm2 = Disasm.disassemble_s prog2 in
  assert_equal_string disasm1 disasm2

let test_disasm_parse prog = function() ->
  let disasm1 = Disasm.disassemble_s prog in
  let prog2 = Parse.program_of_string disasm1 in
  let disasm2 = Disasm.disassemble_s prog2 in
  assert_equal_string disasm1 disasm2

let test_branch = parse
"var x = 9
 var y = 10
 var r = 1
 branch (x == y) $l1 $l2
$l1:
 r <- 2
 goto c
$l2:
 r <- 3
 goto c
c:
 print r
"

let test_branch_pruned =
" var x = 9
 var y = 10
 osr cp_2 [(x == y)] (main, anon, cp_2) [var x = x, var y = y]
 var r = 1
 r <- 3
 print r
"

let test_loop_branch = parse
"var x = 9
 var y = 10
 var r = 1
 goto loop
$loop_b:
 goto loop
loop:
 branch (x == y) $l1 $l2
$l1:
 r <- 2
 goto c
$l2:
 r <- 3
 goto c
c:
 print r
 branch (r == 0) $loop_b $end
$end:
"

let test_loop_branch_pruned =
" var x = 9
 var y = 10
 osr cp_2 [(x == y)] (main, anon, cp_2) [var x = x, var y = y]
 var r = 1
 goto loop
$loop_b:
 goto loop
loop:
 r <- 3
 print r
 branch (r == 0) $loop_b $end
$end:
"

let test_double_loop = parse
"{} var i
 i <- 0
 var sum = 0
 var limit = 4
 goto loop1
loop1:
  branch (i != limit) $loop_body1 $continue
$loop_body1:
   var i2 = 0
   var sum2 = 0
   goto loop2
loop2:
    branch (i2 != limit) $loop_body2 $continue2
$loop_body2:
     print i2
     sum2 <- (sum + i2)
     i2 <- (i2 + 1)
    goto loop2
$continue2:
   sum <- (sum + sum2)
   drop i2
   drop sum2
   i <- (i + 1)
 goto loop1
$continue:
 print sum
"

let test_branch_pruning_exp prog expected =
  let open Transform in
  let prog = try_opt (as_opt_program Transform_assumption.insert_checkpoints) prog in
  let prune = try_opt (combine_opt
                         [branch_prune;
                          (as_opt_function Transform_assumption.hoist_assumption);
                          cleanup_all;
                          (as_opt_function Transform_assumption.remove_empty_osr)]) in
  let prog2 = { prog with main = prune prog.main } in
  assert_equal_string expected
    (Disasm.disassemble_instrs_s (List.hd prog2.main.body).instrs) 

let test_branch_pruning prog deopt =
  let open Eval in
  let open Transform in
  let prog = try_opt (as_opt_program Transform_assumption.insert_checkpoints) prog in
  let prog2 = { prog with main = try_opt branch_prune prog.main } in
  let res1 = Eval.run_forever no_input prog in
  let res2 = Eval.run_forever no_input prog2 in
  assert_equal res1.trace res2.trace;
  assert_equal res2.deopt deopt

let assert_equal_sorted li1 li2 =
  assert_equal (List.sort compare li1) (List.sort compare li2)

let test_pred = parse
"l1:
  goto l2
 l3:
  branch x $l1_a $l2_a
 $l1_a:
  goto l1
 $l2_a:
  goto l2
 l2:
  branch x $l1_b $l3_b
 $l1_b:
  goto l1
 $l3_b:
  goto l3
  stop 0
  goto l1
"

let do_test_pred = function () ->
  let v = Instr.active_version test_pred.main in
  let pred = Analysis.predecessors v.instrs in
  let pred pc = pred.(pc) in
  assert_equal_sorted (pred 0) [5; 11; 15];
  assert_equal_sorted (pred 1) [0];
  assert_equal_sorted (pred 2) [13];
  assert_equal_sorted (pred 4) [3];
  assert_equal_sorted (pred 8) [1; 7];
  assert_equal_sorted (pred 9) [8];
  assert_equal_sorted (pred 14) [];
  assert_equal_sorted (pred 15) []
;;

let test_df = parse
"var a = 1
 var b = 2
 var d = (a+b)
 # space
 b <- 3
 var z = (a+b)
 goto l_
$l1:
 goto l_
$l:
 goto l_
l_:
 var y = (a+b)
 b <- 4
 branch b $l $l2
 # gap
$l2:
 var y = (y+b)
 branch b $l1 $l3
$l3:
"

let do_test_liveness = function () ->
  let open Analysis in
  let v = (as_analysis_input test_df.main (Instr.active_version test_df.main)) in
  let live = live v in
  assert_equal_sorted (live 0) ["a"];
  assert_equal_sorted (live 1) ["a";"b"];
  assert_equal_sorted (live 2) ["a"];
  assert_equal_sorted (live 3) ["a"];
  assert_equal_sorted (live 4) ["a";"b"];
  assert_equal_sorted (live 5) ["a";"b"];
  assert_equal_sorted (live 6) ["a";"b"];
  assert_equal_sorted (live 12)  ["a";"y"];
  assert_equal_sorted (live 13)  ["a";"b";"y"];
  assert_equal_sorted (live 14)  ["a";"b";"y"];
  assert_equal_sorted (live 15) ["a";"b";"y"];
  assert_equal_sorted (live 16) ["a";"b";"y"];
  assert_equal_sorted (live 17) ["a";"b"];
  assert_equal_sorted (live 18) ["a";"b"];
  assert_equal_sorted (live 0) ["a"]
;;


let do_test_used = function () ->
  let open Analysis in
  let v = (as_analysis_input test_df.main (Instr.active_version test_df.main)) in
  let uses = uses v in
  assert_equal_sorted (PcSet.elements (uses 0)) [2;5;12];
  assert_equal_sorted (PcSet.elements (uses 1)) [2];
  assert_equal_sorted (PcSet.elements (uses 2)) [];
  assert_equal_sorted (PcSet.elements (uses 4)) [5;12];
  assert_equal_sorted (PcSet.elements (uses 5)) [];
  assert_equal_sorted (PcSet.elements (uses 12)) [17];
  assert_equal_sorted (PcSet.elements (uses 13)) [12;14;17;18];
  assert_equal_sorted (PcSet.elements (uses 14)) [];
  assert_equal_sorted (PcSet.elements (uses 16)) [];
  assert_equal_sorted (PcSet.elements (uses 17)) [];
  assert_equal_sorted (PcSet.elements (uses 18)) [];
  assert_equal_sorted (PcSet.elements (uses 6)) []
;;


let do_test_reaching = function () ->
  let open Analysis in
  let v = (as_analysis_input test_df.main (Instr.active_version test_df.main)) in
  let reaching = reaching v in
  assert_equal_sorted (PosSet.elements (reaching 0))  [];
  assert_equal_sorted (PosSet.elements (reaching 1))  [];
  assert_equal_sorted (PosSet.elements (reaching 2))  [Analysis.Instr 0; Analysis.Instr 1];
  assert_equal_sorted (PosSet.elements (reaching 5))  [Analysis.Instr 0; Analysis.Instr 4];
  assert_equal_sorted (PosSet.elements (reaching 12))  [Analysis.Instr 13; Analysis.Instr 0; Analysis.Instr 4];
  assert_equal_sorted (PosSet.elements (reaching 17)) [Analysis.Instr 13; Analysis.Instr 12];
  assert_equal_sorted (PosSet.elements (reaching 0))  []

;;

let test_df2 = parse
" goto jmp
$start:
  var i = 1
  var c = 0
  var v = 123
  var x = 0
  loop:
    branch (i==10) $loop_end $loop_begin
  $loop_begin:
    var w = 3
    branch (c==2) $tr $fs
    $tr:
      w <- 3
      goto ct
    $fs:
      branch (c==4) $tr2 $fs2
      $tr2:
        stop 0
    $fs2:
      w <- 4
      goto ct
  ct:
    x <- w
    v <- (c+1)
    i <- (i+v)
    goto loop
$loop_end:
  print i
  print x
  # bla
  goto end
jmp:
  branch true $start $end
$end:
"

let do_test_codemotion = function () ->
  let open Transform in
  let t = parse "
       goto bla
      $loop:
       goto loop_
      loop_:
       y <- z
       x <- (x + y)
       branch (x==10) $end $loop
      $end:
       stop 0
      bla:
       var z = 1
       var x = 1
       var y = z
       goto loop_
  " in
  let expected = parse "
       goto bla
      $loop:
       goto loop_
      loop_:
       x <- (x + y_1)
       branch (x == 10) $end $loop
      $end:
       stop 0
      bla:
       var z = 1
       var y_1 = z
       var x = 1
       var y = z
       goto loop_
  " in
  let res = { t with main = try_opt hoist_assignment t.main } in
  assert_equal_string (Disasm.disassemble_s expected) (Disasm.disassemble_s res);
  let t = parse "
       var x = 1
       var y = 2
       goto loop_
      $loop:
       goto loop_
      loop_:
       y <- 1
       x <- (x + y)
       branch (x==10) $end $loop
      $end:
  " in
  let expected = parse "
       var y_1 = 1
       var x = 1
       var y = 2
       goto loop_
      $loop:
       goto loop_
      loop_:
       x <- (x + y_1)
       branch (x == 10) $end $loop
      $end:
  " in
  let res = { t with main = try_opt hoist_assignment t.main } in
  assert_equal_string (Disasm.disassemble_s expected) (Disasm.disassemble_s res);
  let t = parse "
       var x = 1
       var y = 2
       goto loop_
      $loop:
       goto loop_
      loop_:
       y <- x
       x <- (x + y)
       branch (x==10) $end $loop
      $end:
  " in
  let res = { t with main = try_opt hoist_assignment t.main } in
  (* cannot hoist because depends on previous loop iteration *)
  assert_equal_string (Disasm.disassemble_s t) (Disasm.disassemble_s res);
  let t = parse "
       var x = 1
       var y = 2
       goto loop_
      $loop:
       goto loop_
      loop_:
       branch (x==5) $la $lb
      $la:
       y <- 1
       goto ft
      $lb:
       goto ft
      ft:
       x <- (x + y)
       branch (x==10) $end $loop
      $end:
  " in
  let res = { t with main = try_opt hoist_assignment t.main } in
  (* cannot hoist because if (x==5) then y is modified *)
  assert_equal_string (Disasm.disassemble_s t) (Disasm.disassemble_s res);
  ()

let do_test_minimize_lifetime = function () ->
  let open Transform in
  let t = parse "
       var a = 12
       var b = false
       var c
       branch b $o1 $o2
      $o1:
       a <- 22
       a <- 1
       print a
       goto ft
      $o2:
       goto ft
      ft:
       print b
       drop b
       goto x
      x:
       var b = 3
       print b
       stop 0
  " in
  let expected = parse "
       var a = 12
       var b = false
       branch b $o1 $o2
      $o1:
       a <- 1
       print a
       drop a
       goto ft
      $o2:
       drop a
       goto ft
      ft:
       print b
       drop b
       goto x
      x:
       var b = 3
       print b
       drop b
       stop 0
  " in
  let res = { t with main = try_opt minimize_liverange t.main } in
  assert_equal_string (Disasm.disassemble_s expected) (Disasm.disassemble_s res);
  ()

let do_test_const_fold_driver () =
  let open Transform in
  let test t e =
    let input, expected = (parse t), (parse e) in
    let output = try_opt (as_opt_program const_fold) input in
    if (Disasm.disassemble_s output) <> (Disasm.disassemble_s expected) then begin
      Printf.printf "\ninput: '%s'\noutput: '%s'\nexpected: '%s'\n%!"
        (Disasm.disassemble_s input)
        (Disasm.disassemble_s output)
        (Disasm.disassemble_s expected);
      assert false
    end in

  (* Simple constant propagation test case; sanity check *)
  test {input|
    var x = 1
    print x
  |input} {expect|
    print 1
  |expect};
  (* Constant propagation with some mutation *)
  test {input|
    var w = 0
    var z = w
    w <- 1
    print w
    print z
  |input} {expect|
    var w = 0
    print 1
    print 0
  |expect};
  (* Folding and propagation *)
  test {input|
    var x = 1
    var y = (2 + x)
    var z = (3 + y)
    print z
  |input} {expect|
    print 6
  |expect};
  (* Test with branching *)
  test {input|
    var x = (1 + 0)
    branch (1==1) $l1 $l2
   $l1:
    drop x
    goto next
   $l2:
    print x
    drop x
    goto next
   next:
    var y = 1
    branch (1!=0) $l3 $l4
   $l3:
    print y
    drop y
    stop 0
   $l4:
    drop y
    stop 0
  |input} {expect|
    var x = 1
    branch true $l1 $l2
   $l1:
    drop x
    goto next
   $l2:
    print 1
    drop x
    goto next
   next:
    var y = 1
    branch true $l3 $l4
   $l3:
    print 1
    drop y
    stop 0
   $l4:
    drop y
    stop 0
  |expect};
  (* Test with booleans, updating vars, and branching *)
  test {input|
    var a = 1
    var b = 2
    var ccc = 5
    var cc = ccc
    var c = (cc + 0)
    c <- (a + b)
    var d = true
    branch d $l1 $l2
   $l1:
    c <- (c + a)
    print a
    goto fin
   $l2:
    c <- (c + b)
    print b
    goto fin
   fin:
    print c
    stop 0
  |input} {expect|
    var c = 5
    branch true $l1 $l2
   $l1:
    c <- 4
    print 1
    goto fin
   $l2:
    c <- 5
    print 2
    goto fin
   fin:
    print c
    stop 0
  |expect};
  (* Test with a loop *)
  test {input|
    var n = 10
    goto bla
   $loop:
    goto loop_
   loop_:
    y <- z
    x <- (x + z)
    branch (x==n) $end $loop
   $end:
    print z
    stop 0
   bla:
    var z = 1
    var zz = z
    var x = 1
    var y = (zz + 0)
    goto loop_
  |input} {expect|
    goto bla
   $loop:
    goto loop_
   loop_:
    x <- (x + 1)
    branch (x==10) $end $loop
   $end:
    print 1
    stop 0
   bla:
    var x = 1
    var y = 1
    goto loop_
  |expect};
  (* More complicated control flow *)
  test {input|
    var x = 1
    var t = true
    var a = (10 + 0)
    var b = 20
    var c = 30
    branch t $la $lb
   $la:
    branch t $l1 $l2_a
   $lb:
    branch t $l2_b $l3
   $l1:
    print (a + 0)
    goto fin
   $l2_a:
    goto l2
   $l2_b:
    goto l2
   l2:
    print b
    goto fin
   $l3:
    print c
    goto fin
   fin:
    var y = (x + x)
    print y
    stop 0
  |input} {expect|
    branch true $la $lb
   $la:
    branch true $l1 $l2_a
   $lb:
    branch true $l2_b $l3
   $l1:
    print 10
    goto fin
   $l2_a:
    goto l2
   $l2_b:
    goto l2
   l2:
    print 20
    goto fin
   $l3:
    print 30
    goto fin
   fin:
    print 2
    stop 0
  |expect};
  (* Propagating function references *)
  test {input|
    var f = 'foo
    call x = f ()
   function foo ()
    return 42
  |input} {expect|
    call x = 'foo ()
   function foo ()
    return 42
  |expect};
  (* Constant folding within functions *)
  test {input|
    var a = 1
    var b = 2
    call w = 'f ((a + a))
    call y = 'f (b)
    call z = 'g (b)
   function f (var n)
    var a = (2 + 3)
    return a
   function g (var m)
    var b = (42 + 0)
    # Can't remove assignment
    # Analysis assumes all params might be aliased
    m <- b
    return m
  |input} {expect|
    call w = 'f (2)
    call y = 'f (2)
    call z = 'g (2)
   function f (var n)
    return 5
   function g (var m)
    # Can't remove assignment
    # Analysis assumes all params might be aliased
    m <- 42
    return 42
  |expect};
  (* Constant fold arrays *)
  test {input|
    var zero = 0
    var x = 5
    array a = [4, x]
    a[zero] <- (1 + 2)
  |input} {expect|
    array a = [4, 5]
    a[0] <- 3
  |expect};
  ()

let do_test_pull_drop () =
  let open Transform_hoist in
  let test input pc x expected =
    let input, expected = Instr.active_version input.main, Instr.active_version expected.main in
    let input, expected = input.instrs, expected.instrs in
    let instrs = match try_pull input pc with
      | Pulled_to ((instrs, _), _) -> instrs
      | Blocked -> input in
    assert (instrs = expected);
  in
  let t = parse "
      var e = true
      var x
      branch e $l1 $l2
     $l1:
      drop x
      stop 0
     $l2:
      drop x
    " in
  let e = parse "
      var e = true
      var x
      drop x
      branch e $l1 $l2
     $l1:
      stop 0
     $l2:
  " in
  test t 2 "x" e;
  let t = parse "
      var e = true
      var x
      branch e $l1 $l2
     $l1:
      stop 0
     $l2:
      drop x
    " in
  test t 2 "x" t;
  ()

let do_test_push_drop () =
  let open Transform_hoist in
  let test input pc expected =
    let input, expected = Instr.active_version input.main, Instr.active_version expected.main in
    let input, expected = input.instrs, expected.instrs in
    match[@warning "-4"] input.(pc) with
    | Drop x ->
      let push = push_instr (Drop.conditions_var x) in
      let instrs = match push input pc with
        | Stop (instrs, _) | Work ((instrs, _), _) -> instrs
        | Blocked | Need_pull _ -> input in
      assert (instrs = expected);
    | _ -> assert(false)
  in
  let t = parse "
    var x = 1
    var y = (x + 1)
    var z = y
    drop x
    " in
  let e = parse "
    var x = 1
    var y = (x + 1)
    drop x
    var z = y
  " in
  test t 3 e;
  let t = parse "
    var x = 1
    var y = (x + 1)
    drop x
    " in
  let e = parse "
    var x = 1
    var y = (x + 1)
    drop x
  " in
  test t 2 e;
  let t = parse "
    var x = 1
    read x
    drop x
    " in
  let e = parse "
    var x = 1
    read x
    drop x
  " in
  test t 2 e;
  let t = parse "
    var x = 1
    drop x
    " in
  let e = parse "function main ()
  " in
  test t 1 e;
  let t = parse "
    var x = 1
    x <- 33
    drop x
    " in
  let e = parse "
    var x = 1
    drop x
  " in
  test t 2 e;
  let t = parse "
    var x = 1
    branch (1==1) $l1 $l2
   $l1:
    stop 0
   $l2:
    drop x
    " in
  test t 5 t;
  let t = parse "
    var x = 1
    branch (x==1) $l1 $l2
   $l1:
    stop 0
   $l2:
    drop x
    " in
  test t 5 t;
  let t = parse "
    var x = 1
    branch (1==1) $l1 $l2
   $l1:
    goto ft
   $l2:
    goto ft
   ft:
    drop x
    " in
  let e = parse "
    var x = 1
    branch (1 == 1) $l1 $l2
   $l1:
    drop x
    goto ft
   $l2:
    drop x
    goto ft
   ft:
   " in
  test t 7 e;
  let t = parse "
    var x = 1
    branch (1==1) $e1 $e2
   $e1:
    goto l
   $e2:
    goto l
   l:
    drop x
   " in
  let e = parse "
    var x = 1
    branch (1==1) $e1 $e2
   $e1:
    drop x
    goto l
   $e2:
    drop x
    goto l
   l:
   " in
  test t 7 e;
  let t = parse "
      var a = 1
      call x = bla ()
      drop x
    function bla ()
      return 1
   " in
  test t 2 t;
  ()

let do_test_drop_driver () =
  let test x t e =
    let input, expected = parse t, parse e in
    let input, expected = Instr.active_version input.main, Instr.active_version expected.main in
    let input, expected = input.instrs, expected.instrs in
    let output =
      match Transform_hoist.Drop.pull_var input x with
          | None -> input
          | Some instrs -> instrs in
    if output <> expected then begin
      Printf.printf "input: %s\noutput: %s\nexpected: %s\n%!"
        (Disasm.disassemble_instrs_s input)
        (Disasm.disassemble_instrs_s output)
        (Disasm.disassemble_instrs_s expected);
      assert false
    end in

  test "x" {given|
    var x = 1
    var y = 2
    var z = (y + y)
    drop x
    drop y
  |given} {expect|
    var y = 2
    var z = (y + y)
    drop y
  |expect};
  test "x" {given|
    var x = 1
    var y = 2
    var z = (x + y)
    var w = (y + z)
    drop x
    drop y
  |given} {expect|
    var x = 1
    var y = 2
    var z = (x + y)
    drop x
    var w = (y + z)
    drop y
  |expect};
  test "x" {given|
    var x = 1
    branch (x == 1) $la $lb
   $la:
    print 1
    drop x
    stop 0
   $lb:
    print 2
    drop x
    stop 0
  |given} {expect|
    var x = 1
    branch (x == 1) $la $lb
   $la:
    drop x
    print 1
    stop 0
   $lb:
    drop x
    print 2
    stop 0
  |expect};
  test "x" {given|
    var x = 1
    branch (1 == 1) $la $lb
   $la:
    branch (1 == 1) $l1 $l2_a
   $lb:
    branch (2 == 2) $l2_b $l3
   $l1:
    print 1
    goto die_ende
   $l2_a:
    goto l2
   $l2_b:
    goto l2
   l2:
    print 2
    goto die_ende
   $l3:
    print 3
    goto die_ende
  die_ende:
    drop x
    stop 0
  |given} {expect|
     branch (1 == 1) $la $lb
    $la:
     branch (1 == 1) $l1 $l2_a
    $lb:
     branch (2 == 2) $l2_b $l3
    $l1:
     print 1
     goto die_ende
    $l2_a:
     goto l2
    $l2_b:
     goto l2
    l2:
     print 2
     goto die_ende
    $l3:
     print 3
     goto die_ende
    die_ende:
     stop 0
  |expect};
  ()

let test_functions () =
  let test str n =
    run (parse str) no_input (returns (Int n)) () in
  let test_p str out =
    run (parse str) no_input (trace_is out) () in
  test "return 1\n" 1;
  test "return (1+1)\n" 2;
  test {pr|
     call x = 'bla ()
     return x
    function bla ()
     return 1
  |pr} 1;
  assert_raises
    (Check.ErrorAt ("main", "anon", Check.InvalidNumArgs 0))
    (fun () ->
    test {pr|
       call x = 'bla (1)
      function bla ()
    |pr} 1);
  assert_raises
    (Check.ErrorAt ("bla", "anon", Check.MissingReturn))
    (fun () ->
    test {pr|
       call x = 'bla ()
       return x
      function bla ()
    |pr} 0);
  test {pr|
     call x = 'bla ()
     return x
    function bla ()
      return 123
  |pr} 123;
  test {pr|
     call x = 'bla (22)
     return x
    function bla (var y)
      return y
  |pr} 22;
  test {pr|
     call one = 'one ()
     call three = 'pl (one, 2)
     return three
    function pl (var y, var z)
      return (y+z)
    function one ()
      return 1
  |pr} 3;
  test {pr|
     array a = [3]
     call x = 'bla (a)
     return x[0]
    function bla (var y)
      return y
  |pr} 3;
  test {pr|
     array a = [3]
     call x = 'bla (a)
     return a[0]
    function bla (var y)
     y[0] <- 4
     return false
  |pr} 4;
  assert_raises
    (Check.MissingMain)
    (fun () ->
    test {pr|
      function bla ()
       return false
    |pr} 0);
  assert_raises
    (Check.InvalidMain)
    (fun () ->
    test {pr|
      function main (var x)
       return false
    |pr} 0);
  assert_raises
    (Check.DuplicateParameter ("bla", "x"))
    (fun () ->
    test {pr|
      call x = 'bla (1, 2)
      function bla (var x, var x)
       return false
    |pr} 0);
  test {pr|
     var x = 22
     call y = 'bla (x)
     return y
    function bla (var y)
      return y
  |pr} 22;
  assert_raises
    (Check.ErrorAt ("main", "anon", Check.FunctionDoesNotExist "x"))
    (fun () ->
    test {pr|
       call y = 'x ()
    |pr} 0);
  assert_raises
    (Check.ErrorAt ("main", "anon", Check.FunctionDoesNotExist "x"))
    (fun () ->
    test {pr|
       var x = 'x
    |pr} 0);
  test_p {pr|
     var x = 'bla
     call y = x (x)
     print y
    function bla (var y)
      return y
  |pr} [(Fun_ref "bla")];
  test {pr|
     var x = 'bla
     call y = x ('bla2)
     return y
    function bla (var y)
      call r = y ()
      return r
    function bla2 ()
      return 33
  |pr} 33;
  let open Eval in
  assert_raises (Eval.Type_error {expected = Eval.Fun_ref; received = Eval.Int})
    (fun () ->
     test {pr|
       var x = 1
       call y = x ()
       return y
    |pr} 33);
  ();;

let do_test_array () =
  let test filename p =
    run (Parse.program_of_file filename) no_input p () in

  test "examples/array.sou" (trace_is [Int 1; Int 2; Int 3; Int 4; Int 5;
                                       Int 6; Int 7; Int 8; Int 9; Int 10]);
  test "examples/array_sum.sou" (trace_is [Int 55]);
  ()

let do_test_deopt () =
  let test str n =
    run (parse str) no_input (returns (Int n)) () in

  test {pr|
    function main ()
    version a
     var x = 1
     osr l [(x==1)] (main, b, l) [var y=42]
     return x

    version b
     var y = 2
     osr l [] (main, b, l) [var y=y]
     return y
  |pr} 42;

  test {pr|
    function main ()
     call x = 'foo()
     return x
    function foo()
    version vers_a
     osr l [(1==1)] (foo,vers_b,l) [var x = (41 + 1)]
     return 0
    version vers_b
     var x = 0
     osr l [] (foo,vers_b,l) [var x = x]
     return x
  |pr} 42;
  ()

let do_test_assert () =
  let postcondition = has_var "x" (Value.int 2) in
  let assert_true = parse {|
    var x = 2
    assert (x == 2)
  |} in
  let assert_false = parse {|
    var x = 2
    assert (x == 3)
  |} in
  run assert_true no_input postcondition ();
  assert_raises
    (Eval.User_assert_failure {func="main";version="anon";pos=1})
    (run assert_false no_input postcondition)

let suite =
  "suite">:::
  ["var">:: run test_var no_input
     (has_var "x" (Value.int 2)
      &&& (trace_is Value.[int 1; int 2]));
   "decl_var">:: run test_decl_var no_input
     (has_var "x" (Value.int 1));
   "incr_var">:: run test_incr_var no_input
     (has_var "x" (Value.int 2));
   "print">:: run test_print no_input
     (trace_is Value.[int 1; int 2]);
   "assert">:: do_test_assert;
   "jump">:: run test_jump no_input
     (has_var "x" (Value.bool true));
   "jump (oo)" >:: run test_overloading no_input
     (has_var "b" (Value.bool true)
      &&& has_var "x" (Value.int 2)
      &&& has_var "y" (Value.int 1));
   "neg">:: run (test_neg 1) no_input
     (has_var "y" (Value.int (-1)));
   "neg2">:: run (test_neg (-1)) no_input
     (has_var "y" (Value.int 1));
   "add">:: run (test_add "1" "2") no_input
     (has_var "z" (Value.int 3));
   "add2">:: run (test_add "2" "1") no_input
     (has_var "z" (Value.int 3));
   "sub">:: run (test_sub "1" "2") no_input
     (has_var "z" (Value.int (-1)));
   "sub2">:: run (test_sub "2" "1") no_input
     (has_var "z" (Value.int 1));
   "mult">:: run (test_mult "1" "2") no_input
     (has_var "z" (Value.int 2));
   "mult2">:: run (test_mult "2" "1") no_input
     (has_var "z" (Value.int 2));
   "div">:: run (test_div "1" "2") no_input
     (has_var "z" (Value.int 0));
   "div2">:: run (test_div "2" "1") no_input
     (has_var "z" (Value.int 2));
   "div3">::
   (fun () -> assert_raises (Eval.Division_by_zero)
       (run_unchecked (test_div "1" "0") no_input ok));
   "mod">:: run (test_mod "1" "2") no_input
     (has_var "z" (Value.int 1));
   "mod2">:: run (test_mod "2" "1") no_input
     (has_var "z" (Value.int 0));
   "mod3">::
   (fun () -> assert_raises (Eval.Division_by_zero)
       (run_unchecked (test_mod "1" "0") no_input ok));
   "eq">:: run (test_eq 1 2) no_input
     (has_var "z" (Value.bool false));
   "eq2">:: run (test_eq 1 1) no_input
     (has_var "z" (Value.bool true));
   "neq">:: run (test_neq 1 2) no_input
     (has_var "z" (Value.bool true));
   "neq2">:: run (test_neq 1 1) no_input
     (has_var "z" (Value.bool false));
   "lt">:: run (test_lt 1 2) no_input
     (has_var "z" (Value.bool true));
   "lt2">:: run (test_lt 2 1) no_input
     (has_var "z" (Value.bool false));
   "lt3">:: run (test_lt 1 1) no_input
     (has_var "z" (Value.bool false));
   "lte">:: run (test_lte 1 2) no_input
     (has_var "z" (Value.bool true));
   "lt2">:: run (test_lte 2 1) no_input
     (has_var "z" (Value.bool false));
   "lt3">:: run (test_lte 1 1) no_input
     (has_var "z" (Value.bool true));
   "gt">:: run (test_gt 1 2) no_input
     (has_var "z" (Value.bool false));
   "gt2">:: run (test_gt 2 1) no_input
     (has_var "z" (Value.bool true));
   "gt3">:: run (test_gt 1 1) no_input
     (has_var "z" (Value.bool false));
   "gte">:: run (test_gte 1 2) no_input
     (has_var "z" (Value.bool false));
   "gte2">:: run (test_gte 2 1) no_input
     (has_var "z" (Value.bool true));
   "gte3">:: run (test_gte 1 1) no_input
     (has_var "z" (Value.bool true));
   "not">:: run (test_not true) no_input
     (has_var "y" (Value.bool false));
   "not2">:: run (test_not false) no_input
     (has_var "y" (Value.bool true));
   "and">:: run (test_and true true) no_input
     (has_var "z" (Value.bool true));
   "and2">:: run (test_and true false) no_input
     (has_var "z" (Value.bool false));
   "and3">:: run (test_and false true) no_input
     (has_var "z" (Value.bool false));
   "and4">:: run (test_and false false) no_input
     (has_var "z" (Value.bool false));
   "or">:: run (test_or true true) no_input
     (has_var "z" (Value.bool true));
   "or2">:: run (test_or true false) no_input
     (has_var "z" (Value.bool true));
   "or3">:: run (test_or false true) no_input
     (has_var "z" (Value.bool true));
   "or4">:: run (test_or false false) no_input
     (has_var "z" (Value.bool false));
   "loops">:: run (test_sum 5) no_input
     (has_var "sum" (Value.int 10));
   "read">:: run test_read_print (input [Value.bool false; Value.int 1])
     (trace_is Value.[int 1; bool false]);
   "mut_undeclared">::
   (fun () -> assert_raises (Eval.Unbound_variable "b")
       (run_unchecked test_read_print_err
          (input [Value.bool false; Value.int 1]) ok));
   "mut_undeclared2">::
   (fun () -> assert_raises (Scope.ScopeExceptionAt("main", "anon", (Scope.UndeclaredVariable (VarSet.singleton "b", 1))))
       (fun() -> Scope.check_function test_read_print_err.main));
   "mut_undeclared3">::
   (fun () -> assert_raises (Scope.ScopeExceptionAt("main", "anon", (Scope.UndeclaredVariable (VarSet.singleton "b", 6))))
       (fun() -> Scope.check_function test_read_print_err_3.main));
   "scope1">:: infer_broken_scope test_broken_scope_1 (undeclared ["x"] 0);
   "scope2">:: infer_broken_scope test_broken_scope_2 (undeclared ["x"] 3);
   "scope3">:: infer_broken_scope test_broken_scope_3 (undeclared ["x"] 9);
   "scope4">:: infer_broken_scope test_broken_scope_4 (extraneous ["y"] 2);
   "scope4fixed">:: run test_broken_scope_4_fixed no_input ok;
   "scope5">:: infer_broken_scope test_broken_scope_5 (undeclared ["w"] 2);
   "scope1ok">:: run (test_scope_1 "c" "c") no_input
     (has_var "c" (Value.int 0));
   "scope1broken">:: infer_broken_scope
     (test_scope_1 "a" "c") (undeclared ["a"] 14);
   "scope1broken2">:: infer_broken_scope
     (test_scope_1 "a" "b") (undeclared ["b"; "a"] 14);
   "parser">:: test_parse_disasm   ("stop 0\n");
   "parser1">:: test_parse_disasm  ("var x = 3\nprint x\nstop 0\n");
   "parser2">:: test_parse_disasm  ("goto l\nx <- 3\nl:\n");
   "parser3">:: test_parse_disasm  ("var x = (y + x)\n");
   "parser4">:: test_parse_disasm  ("x <- (x == y)\n");
   "parser5">:: test_parse_disasm  ("# asdfasdf\n");
   "parser5b">:: test_parse_disasm ("osr l [(x == y)] (f, v, l) [var x = x, var v, var x = (1+2)]\nl:\n");
   "parser6">:: test_parse_disasm  ("branch (x == y) $as $fd\n");
   "parser7">:: test_parse_disasm  ("var x = (y + x)\n x <- (x == y)\n# asdfasdf\nbranch (x == y) $as $fd\n");
   "parser8">:: test_parse_disasm_file "examples/sum.sou";
   "parser_arr1">:: test_parse_disasm ("array x[10]\n");
   "parser_arr2">:: test_parse_disasm ("array x = []\narray x = [1, x, nil]\n");
   "parser_arr3">:: test_parse_disasm ("var x = y[10]\n");
   "parser_arr4">:: test_parse_disasm ("var x = length(y)\n");
   "parser_arr_file">:: test_parse_disasm_file "examples/array_sum.sou";
   "disasm1">:: test_disasm_parse (test_sum 10);
   "disasm2">:: test_disasm_parse (test_add "1" "0");
   "disasm3">:: test_disasm_parse (test_sub "1" "0");
   "disasm4">:: test_disasm_parse (test_mult "1" "0");
   "disasm5">:: test_disasm_parse (test_div "1" "0");
   "disasm6">:: test_disasm_parse (test_mod "1" "0");
   "disasm7">:: test_disasm_parse (test_eq 1 0);
   "disasm8">:: test_disasm_parse (test_neq 1 0);
   "disasm9">:: test_disasm_parse (test_lt 1 0);
   "disasm10">:: test_disasm_parse (test_lte 1 0);
   "disasm11">:: test_disasm_parse (test_gt 1 0);
   "disasm12">:: test_disasm_parse (test_gte 1 0);
   "disasm13">:: test_disasm_parse (test_and true false);
   "disasm14">:: test_disasm_parse (test_or true false);
   "disasm15">:: test_disasm_parse (test_neg 1);
   "disasm16">:: test_disasm_parse (test_not true);
   "disasm_scope1">:: test_disasm_parse test_broken_scope_4;
   "disasm_scope2">:: test_disasm_parse test_broken_scope_4_fixed;
   "disasm_scope3">:: test_disasm_parse test_broken_scope_5;
   "parser_scope1">:: test_parse_disasm "function main()\nversion active\n{a, b} print x\n{a,x,...} #asdf\n";
   "branch_pruning">:: (fun () -> test_branch_pruning_exp test_branch test_branch_pruned);
   "branch_pruning2">:: (fun () -> test_branch_pruning_exp test_loop_branch test_loop_branch_pruned);
   "predecessors">:: do_test_pred;
   "branch_pruning_eval">:: (fun () -> test_branch_pruning test_branch None);
   "branch_pruning_eval2">:: (fun () -> test_branch_pruning (test_sum 10) (Some "cp_6"));
   "branch_pruning_eval3">:: (fun () -> test_branch_pruning test_double_loop (Some "cp_6"));
   "reaching">:: do_test_reaching;
   "used">:: do_test_used;
   "liveness">:: do_test_liveness;
   "codemotion">:: do_test_codemotion;
   "min_lifetimes">:: do_test_minimize_lifetime;
   "constant_fold">:: do_test_const_fold_driver;
   "push_drop">:: do_test_push_drop;
   "pull_drop">:: do_test_pull_drop;
   "move_drop">:: do_test_drop_driver;
   "test_functions">:: test_functions;
   "deopt">:: do_test_deopt;
   "array">:: do_test_array;
   ]
;;

(* use this instead of run_test_tt_main below
   if you want to be able to see the backtrace
   raised by an in-test exception with OCAMLRUNPARAM=b
*)
let run_test_raw  testsuite =
  let rec run = function
    | TestCase test_fun -> test_fun ()
    | TestLabel (_label, test) -> run test
    | TestList tests -> List.iter run tests
  in run testsuite

let () =
  let test_result = run_test_tt_main suite in
  let is_success = function[@warning "-4"]
    | RSuccess _ -> true
    | _ -> false in
  if not (List.for_all is_success test_result) then exit 1;;
