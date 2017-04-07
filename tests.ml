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

let exact vars = Some Scope.(ExactScope (VarSet.of_list vars))
let at_least vars = Some Scope.(AtLeastScope (VarSet.of_list vars))

let parse str : program =
  try Parse.program_of_string str
  with Parse.Error error ->
    Parse.report_error error;
    exit 2

let test_print = parse
" print 1
  print 2
  stop 0
"

let test_decl_const = parse
" const x  = 1
  print x
  stop 0
"

let test_mut = parse
" mut x = 1
  print x
  x <- 2
  print x
  stop 0
"

let test_jump = parse
" mut x = true
  goto jmp
  x <- false
 jmp:
"

let test_overloading = parse
" mut b = true
  mut x = 1
  const y = x
  goto jump
  b <- false
 jump:
  x <- 2
  stop 0
"

let test_add a b = parse (
" mut x = "^a^"
  mut y = "^b^"
  mut z = (x + y)
")

let test_eq a b = parse (
" mut x = "^ string_of_int a ^"
  mut y = "^ string_of_int b ^"
  const z = (x==y)
")

let test_sum limit_ = parse (
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
  stop 0
")

let test_broken_scope_1 = parse
" print x
"

let test_broken_scope_2 = parse
" goto l
  const x = 0
 l:
  print x
"

let test_broken_scope_3 = parse
" const y = false
  branch y cont next
 next:
  const x = 0
  drop x
 cont:
  print x
"

let test_broken_scope_4 = parse
"mut x = 0
mut y = 0
{x} mut z = false
z <- (x == y)
"

let test_broken_scope_4_fixed = parse
"mut x = 0
mut y = 0
{x, ...} mut z = false
z <- (x == y)
"

let test_broken_scope_5 = parse
"mut x = 0
mut y = 0
{w, ...} mut z = false
z <- (x == y)
"

let test_scope_1 test_var1 test_var2 = parse (
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

let test_read_print = parse
"   mut n
    mut b
    read b
    read n
    print n
    drop n
    print b
    drop b
"
let test_read_print_err = parse
"   mut n
    read b
    read n
    print n
    print b
"
let test_read_print_err_2 = parse
"   mut n
    mut b
    read b
    print n
    print b
"
let test_read_print_err_3 = parse
"   mut n
    mut b
    read b
    read n
    drop b
    print n
    print b
"
let test_read_print_err_4 = parse
"   mut n
    mut b
    read b
    read n
    clear b
    print n
    print b
"

let do_test_scope_uninitialized = function () ->
  assert_raises (Scope.ScopeExceptionAt("main", "anon", Scope.UninitializedVariable (VarSet.singleton "x", 2)))
    (fun () -> Scope.check_program (parse "
     mut x = 1
    loop:
     print x
     clear x
     goto loop
    "));
  assert_raises (Scope.ScopeExceptionAt("main", "anon", (Scope.UninitializedVariable (VarSet.singleton "x", 2))))
    (fun () -> Scope.check_program (parse "
     mut x = 1
    loop:
     print x
     branch (x==1) clearit loop
    clearit:
     clear x
     goto loop
    "));
  (* Positive example: even though one branch cleares x it is restored at the end *)
  ignore (parse "
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
  Scope.ScopeExceptionAt("main", "anon", Scope.UndeclaredVariable (VarSet.of_list missing_vars, pos))

let extraneous extra_vars pos =
  Scope.ScopeExceptionAt("main", "anon", Scope.ExtraneousVariable (VarSet.of_list extra_vars, pos))

let infer_broken_scope program exn = function() ->
  let test () = Scope.check_program program in
  assert_raises exn test

let test_parse_disasm_file file = function() ->
  let prog1 = Parse.program_of_file file in
  let disasm1 = Disasm.disassemble_s prog1 in
  let prog2 = Parse.program_of_string disasm1 in
  let disasm2 = Disasm.disassemble_s prog2 in
  assert_equal disasm1 disasm2

let test_parse_disasm str = function() ->
  let prog1 = Parse.program_of_string str in
  let disasm1 = Disasm.disassemble_s prog1 in
  let prog2 = Parse.program_of_string disasm1 in
  let disasm2 = Disasm.disassemble_s prog2 in
  assert_equal disasm1 disasm2

let test_disasm_parse prog = function() ->
  let disasm1 = Disasm.disassemble_s prog in
  let prog2 = Parse.program_of_string disasm1 in
  let disasm2 = Disasm.disassemble_s prog2 in
  assert_equal disasm1 disasm2

let test_branch = parse
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
"function main ()
version anon_1
 mut x = 9
 mut y = 10
 mut r = 1
 osr [(x == y)] (main, anon, l1) [mut r, mut x, mut y]
 r <- 3
 print r
 clear r
version anon
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

let test_double_loop = parse
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
  let open Transform in
  let prog2 = { prog with main = try_opt branch_prune prog.main } in
  assert_equal (Disasm.disassemble_s prog2) expected

let test_branch_pruning prog deopt =
  let open Eval in
  let open Transform in
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
  branch x l1 l2
 l2:
  branch x l1 l3
  stop 0
  goto l1
"

let do_test_pred = function () ->
  let v = Instr.active_version test_pred.main in
  let pred = Analysis.predecessors v.instrs in
  let pred pc = pred.(pc) in
  assert_equal_sorted (pred 0) [3; 5; 7];
  assert_equal_sorted (pred 1) [0];
  assert_equal_sorted (pred 2) [5];
  assert_equal_sorted (pred 3) [2];
  assert_equal_sorted (pred 4) [1; 3];
  assert_equal_sorted (pred 5) [4];
  assert_equal_sorted (pred 6) [];
  assert_equal_sorted (pred 7) []

let test_df = parse
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
  assert_equal_sorted (live 7)  ["a";"y"];
  assert_equal_sorted (live 8)  ["a";"b";"y"];
  assert_equal_sorted (live 9)  ["a";"b";"y"];
  assert_equal_sorted (live 11) ["a";"b";"y"];
  assert_equal_sorted (live 12) ["a";"b"];
  assert_equal_sorted (live 13) ["a";"b"];
  assert_equal_sorted (live 0) ["a"]


let do_test_used = function () ->
  let open Analysis in
  let v = (as_analysis_input test_df.main (Instr.active_version test_df.main)) in
  let uses = uses v in
  assert_equal_sorted (PcSet.elements (uses 0)) [2;5;7];
  assert_equal_sorted (PcSet.elements (uses 1)) [2];
  assert_equal_sorted (PcSet.elements (uses 2)) [];
  assert_equal_sorted (PcSet.elements (uses 4)) [5;7];
  assert_equal_sorted (PcSet.elements (uses 5)) [];
  assert_equal_sorted (PcSet.elements (uses 7)) [12];
  assert_equal_sorted (PcSet.elements (uses 8)) [7;9;12;13];
  assert_equal_sorted (PcSet.elements (uses 9)) [];
  assert_equal_sorted (PcSet.elements (uses 11)) [];
  assert_equal_sorted (PcSet.elements (uses 12)) [];
  assert_equal_sorted (PcSet.elements (uses 13)) [];
  assert_equal_sorted (PcSet.elements (uses 6)) []


let do_test_reaching = function () ->
  let open Analysis in
  let v = (as_analysis_input test_df.main (Instr.active_version test_df.main)) in
  let reaching = reaching v in
  assert_equal_sorted (PosSet.elements (reaching 0))  [];
  assert_equal_sorted (PosSet.elements (reaching 1))  [];
  assert_equal_sorted (PosSet.elements (reaching 2))  [Analysis.Instr 0; Analysis.Instr 1];
  assert_equal_sorted (PosSet.elements (reaching 5))  [Analysis.Instr 0; Analysis.Instr 4];
  assert_equal_sorted (PosSet.elements (reaching 7))  [Analysis.Instr 8; Analysis.Instr 0; Analysis.Instr 4];
  assert_equal_sorted (PosSet.elements (reaching 12)) [Analysis.Instr 8; Analysis.Instr 7];
  assert_equal_sorted (PosSet.elements (reaching 0))  []

let test_df2 = parse
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
        stop 0
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

let do_test_codemotion = function () ->
  let open Transform in
  let t = parse "
       goto bla
      loop:
       y <- z
       x <- (x + y)
       branch (x==10) end loop
      end:
       stop 0
      bla:
       const z = 1
       mut x = 1
       mut y = z
       goto loop
  " in
  let expected = parse "
       goto bla
      loop:
       x <- (x + y_1)
       branch (x == 10) end loop
      end:
       stop 0
      bla:
       const z = 1
       mut y_1 = z
       mut x = 1
       mut y = z
       goto loop
  " in
  let res = { t with main = try_opt hoist_assignment t.main } in
  assert_equal (Disasm.disassemble_s res) (Disasm.disassemble_s expected);
  let t = parse "
       mut x = 1
       mut y = 2
      loop:
       y <- 1
       x <- (x + y)
       branch (x==10) end loop
      end:
  " in
  let expected = parse "
       mut y_1 = 1
       mut x = 1
       mut y = 2
      loop:
       x <- (x + y_1)
       branch (x == 10) end loop
      end:
  " in
  let res = { t with main = try_opt hoist_assignment t.main } in
  assert_equal (Disasm.disassemble_s res) (Disasm.disassemble_s expected);
  let t = parse "
       mut x = 1
       mut y = 2
      loop:
       y <- x
       x <- (x + y)
       branch (x==10) end loop
      end:
  " in
  let res = { t with main = try_opt hoist_assignment t.main } in
  (* cannot hoist because depends on previous loop iteration *)
  assert_equal (Disasm.disassemble_s res) (Disasm.disassemble_s t);
  let t = parse "
       mut x = 1
       mut y = 2
      loop:
       branch (x==5) la lb
      la:
       y <- 1
      lb:
       x <- (x + y)
       branch (x==10) end loop
      end:
  " in
  let res = { t with main = try_opt hoist_assignment t.main } in
  (* cannot hoist because if (x==5) then y is modified *)
  assert_equal (Disasm.disassemble_s res) (Disasm.disassemble_s t);
  ()

let do_test_minimize_lifetime = function () ->
  let open Transform in
  let t = parse "
       mut a = 12
       mut b = false
       mut c
       branch b o1 o2
      o1:
       a <- 22
       a <- 1
       print a
      o2:
       print b
       drop b
       goto x
      x:
       const b = 3
       print b
       stop 0
  " in
  let expected = parse "
       mut a = 12
       mut b = false
       branch b o1 o2
      o1:
       a <- 1
       print a
      o2:
       drop a
       print b
       drop b
       goto x
      x:
       const b = 3
       print b
       drop b
       stop 0
  " in
  let res = { t with main = try_opt minimize_liverange t.main } in
  assert_equal (Disasm.disassemble_s res) (Disasm.disassemble_s expected);
  ()

let do_test_const_prop_driver () =
  let open Transform in
  let test t e =
    let input, expected = (parse t), (parse e) in
    let output = { input with main = try_opt const_prop input.main } in
    if (active_version output.main).instrs <> (active_version expected.main).instrs then begin
      Printf.printf "input: '%s'\noutput: '%s'\nexpected: '%s'\n%!"
        (Disasm.disassemble_s input)
        (Disasm.disassemble_s output)
        (Disasm.disassemble_s expected);
      assert false
    end in

  (* Simple test case; sanity check *)
  test {input|
    const x = 1
    print x
  |input} {expect|
    print 1
  |expect};
  (* Test with branching *)
  test {input|
    const x = 1
    branch (1==1) l1 l2
   l1:
    drop x
    goto next
   l2:
    print x
    drop x
    goto next
   next:
    const y = 1
    branch (1==1) l3 l4
   l3:
    print y
    drop y
    stop 0
   l4:
    drop y
    stop 0
  |input} {expect|
    const x = 1
    branch (1==1) l1 l2
   l1:
    drop x
    goto next
   l2:
    print 1
    drop x
    goto next
   next:
    const y = 1
    branch (1==1) l3 l4
   l3:
    print 1
    drop y
    stop 0
   l4:
    drop y
    stop 0
  |expect};
  (* Test with booleans, updating mut vars, and branching *)
  test {input|
    const a = 1
    const b = 2
    mut c = 5
    c <- (a + b)
    const d = true
    branch d l1 l2
   l1:
    c <- (c + a)
    print a
    goto fin
   l2:
    c <- (c + b)
    print b
    goto fin
   fin:
    print c
    stop 0
  |input} {expect|
    mut c = 5
    c <- (1 + 2)
    branch true l1 l2
   l1:
    c <- (c + 1)
    print 1
    goto fin
   l2:
    c <- (c + 2)
    print 2
    goto fin
   fin:
    print c
    stop 0
  |expect};
  (* Test with a loop *)
  test {input|
    const n = 10
    goto bla
   loop:
    y <- z
    x <- (x + z)
    branch (x==n) end loop
   end:
    print z
    stop 0
   bla:
    const z = 1
    mut x = 1
    mut y = z
    goto loop
  |input} {expect|
    goto bla
   loop:
    x <- (x + 1)
    branch (x==10) end loop
   end:
    print 1
    stop 0
   bla:
    mut x = 1
    mut y = 1
    goto loop
  |expect};
  (* More complicated control flow *)
  test {input|
    const x = 1
    const t = true
    const a = 10
    const b = 20
    const c = 30
    branch t la lb
   la:
    branch t l1 l2
   lb:
    branch t l2 l3
   l1:
    print a
    goto fin
   l2:
    print b
    goto fin
   l3:
    print c
    goto fin
   fin:
    const y = (x + x)
    print y
    stop 0
  |input} {expect|
    branch true la lb
   la:
    branch true l1 l2
   lb:
    branch true l2 l3
   l1:
    print 10
    goto fin
   l2:
    print 20
    goto fin
   l3:
    print 30
    goto fin
   fin:
    const y = (1 + 1)
    print y
    stop 0
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
      mut e = true
      mut x
      branch e l1 l2
     l1:
      drop x
      stop 0
     l2:
      drop x
    " in
  let e = parse "
      mut e = true
      mut x
      drop x
      branch e l1 l2
     l1:
      stop 0
     l2:
  " in
  test t 2 "x" e;
  let t = parse "
      mut e = true
      mut x
      branch e l1 l2
     l1:
      stop 0
     l2:
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
    const x = 1
    const y = (x + 1)
    const z = y
    drop x
    " in
  let e = parse "
    const x = 1
    const y = (x + 1)
    drop x
    const z = y
  " in
  test t 3 e;
  let t = parse "
    const x = 1
    const y = (x + 1)
    drop x
    " in
  let e = parse "
    const x = 1
    const y = (x + 1)
    drop x
  " in
  test t 2 e;
  let t = parse "
    mut x = 1
    read x
    drop x
    " in
  let e = parse "
    mut x = 1
    read x
    drop x
  " in
  test t 2 e;
  let t = parse "
    mut x = 1
    drop x
    " in
  let e = parse "function main ()
  " in
  test t 1 e;
  let t = parse "
    mut x = 1
    x <- 33
    drop x
    " in
  let e = parse "
    mut x = 1
    drop x
  " in
  test t 2 e;
  let t = parse "
    mut x = 1
    branch (1==1) l1 l2
   l1:
    stop 0
   l2:
    drop x
    " in
  test t 5 t;
  let t = parse "
    mut x = 1
    branch (x==1) l1 l2
   l1:
    stop 0
   l2:
    drop x
    " in
  test t 5 t;
  let t = parse "
    mut x = 1
    branch (1==1) l1 l2
   l1:
    goto l2
   l2:
    drop x
    " in
  let e = parse "
    mut x = 1
    branch (1 == 1) l1 l2_1
   l1:
    goto l2
   l2_1:
    goto l2
   l2:
    drop x
   " in
  test t 5 e;
  let t = parse "
    mut x = 1
    branch (1==1) e1 e2
   e1:
    goto l
   e2:
    goto l
   l:
    drop x
   " in
  let e = parse "
    mut x = 1
    branch (1==1) e1 e2
   e1:
    drop x
    goto l
   e2:
    drop x
    goto l
   l:
   " in
  test t 7 e;
  let t = parse "
      const a = 1
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
    const x = 1
    const y = 2
    const z = (y + y)
    drop x
    drop y
  |given} {expect|
    const y = 2
    const z = (y + y)
    drop y
  |expect};
  test "x" {given|
    const x = 1
    const y = 2
    const z = (x + y)
    const w = (y + z)
    drop x
    drop y
  |given} {expect|
    const x = 1
    const y = 2
    const z = (x + y)
    drop x
    const w = (y + z)
    drop y
  |expect};
  test "x" {given|
    const x = 1
    branch (x == 1) la lb
   la:
    print 1
    drop x
    stop 0
   lb:
    print 2
    drop x
    stop 0
  |given} {expect|
    const x = 1
    branch (x == 1) la lb
   la:
    drop x
    print 1
    stop 0
   lb:
    drop x
    print 2
    stop 0
  |expect};
  test "x" {given|
    const x = 1
    branch (1 == 1) la lb
   la:
    branch (1 == 1) l1 l2
   lb:
    branch (2 == 2) l2 l3
   l1:
    print 1
    goto die_ende
   l2:
    print 2
    goto die_ende
   l3:
    print 3
    goto die_ende
  die_ende:
    drop x
    stop 0
  |given} {expect|
     branch (1 == 1) la lb
    la:
     branch (1 == 1) l1 l2_2
    lb:
     branch (2 == 2) l2_1 l3
    l1:
     print 1
     goto die_ende
    l2_1:
     goto l2
    l2_2:
     goto l2
    l2:
     print 2
     goto die_ende
    l3:
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
    function bla (const y)
      return y
  |pr} 22;
  test {pr|
     call one = 'one ()
     call three = 'pl (one, 2)
     return three
    function pl (const y, const z)
      return (y+z)
    function one ()
      return 1
  |pr} 3;
  assert_raises
    (Check.ErrorAt ("main", "anon", Check.InvalidArgument (0, (Arg_by_val (Simple (Constant (Int 22)))))))
    (fun () ->
    test {pr|
       call x = 'bla (22)
       return x
      function bla (mut y)
        return y
    |pr} 22);
  test {pr|
     mut a = 3
     call x = 'bla (&a)
     return x
    function bla (mut y)
      return y
  |pr} 3;
  test {pr|
     mut a = 3
     call x = 'bla (&a)
     return a
    function bla (mut y)
     y <- 4
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
      function main (const x)
       return false
    |pr} 0);
  assert_raises
    (Check.DuplicateParameter ("bla", "x"))
    (fun () ->
    test {pr|
      call x = 'bla (1, 2)
      function bla (const x, const x)
       return false
    |pr} 0);
  assert_raises
    (Check.ErrorAt ("main", "anon", Check.InvalidArgument (1, (Arg_by_val (Simple (Var "x"))))))
    (fun () ->
    test {pr|
       mut x = 22
       call y = 'bla (x)
      function bla (mut y)
        return y
    |pr} 22);
  test {pr|
     mut x = 22
     call y = 'bla (x)
     return y
    function bla (const y)
      return y
  |pr} 22;
  assert_raises
    (Check.ErrorAt ("main", "anon", Check.InvalidArgument (1, (Arg_by_val (Simple (Var "x"))))))
    (fun () ->
    test {pr|
       const x = 22
       call y = 'bla (x)
      function bla (mut y)
        return y
    |pr} 22);
  assert_raises
    (Check.ErrorAt ("main", "anon", Check.InvalidArgument (1, (Arg_by_ref "x"))))
    (fun () ->
    test {pr|
       const x = 22
       call y = 'bla (&x)
      function bla (mut y)
        return y
    |pr} 22);
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
       const x = 'x
    |pr} 0);
  test_p {pr|
     mut x = 'bla
     call y = x (x)
     print y
    function bla (const y)
      return y
  |pr} [(Fun_ref "bla")];
  test {pr|
     mut x = 'bla
     call y = x ('bla2)
     return y
    function bla (const y)
      call r = y ()
      return r
    function bla2 ()
      return 33
  |pr} 33;
  assert_raises
    (Check.ErrorAt ("main", "anon", Check.InvalidArgument (1, (Arg_by_ref "x"))))
    (fun () ->
    test {pr|
       const x = 22
       call y = 'bla (&x)
      function bla (mut y)
        return y
    |pr} 22);
  let open Eval in
  assert_raises (Eval.Type_error {expected = Eval.Fun_ref; received = Eval.Int})
    (fun () ->
     test {pr|
       mut x = 1
       call y = x ()
       return y
    |pr} 33);
  assert_raises
    (Check.ErrorAt ("main", "anon", Check.InvalidArgument (2, (Arg_by_ref "x"))))
    (fun () ->
    test {pr|
       const x = 22
       const func = 'bla
       call y = func (&x)
      function bla (mut y)
        return y
    |pr} 22);
  assert_raises
    (Eval.InvalidArgument)
    (fun () ->
    test {pr|
       const x = 22
       const func = 'bla
       call y = func (x)
      function bla (mut y)
        return y
    |pr} 22);
  ();;

let do_test_mut_to_const () =
  let open Transform in
  let test t e =
    let input, expected = (parse t), (parse e) in
    let output = { input with main = try_opt make_constant input.main } in
    if (active_version output.main).instrs <> (active_version expected.main).instrs then begin
      Printf.printf "input: '%s'\noutput: '%s'\nexpected: '%s'\n%!"
        (Disasm.disassemble_s input)
        (Disasm.disassemble_s output)
        (Disasm.disassemble_s expected);
      assert false
    end in

  test {input|
    mut x = 1
    print x
  |input} {expect|
    const x = 1
    print x
  |expect};
  test {input|
    mut x = 1
    x <- 1
    print x
  |input} {expect|
    mut x = 1
    x <- 1
    print x
  |expect};
  test {input|
    mut x = 1
    call y = x (&x)
    print x
  |input} {expect|
    mut x = 1
    call y = x (&x)
    print x
  |expect};
  test {input|
    mut x = 1
    mut y = (x+1)
    print y
  |input} {expect|
    const x = 1
    const y = (x+1)
    print y
  |expect};
  ();;

let do_test_array () =
  let test filename value =
    run (Parse.program_of_file filename) no_input (trace_is [value]) () in

  test "examples/array.sou" (Array [|Int 1; Int 2; Int 3; Int 4; Int 5;
                                     Int 6; Int 7; Int 8; Int 9; Int 10|]);
  test "examples/array_sum.sou" (Int 55);
  ()

let do_test_deopt () =
  let test str n =
    run (parse str) no_input (returns (Int n)) () in

  test {pr|
    function main ()
    version a
     const x = 1
     osr [(x==1)] (main, b, l) [const y=42]
     return x

    version b
     const y = 2
    l:
     return y
  |pr} 42;

  test {pr|
    function main ()
     mut aliased = 33
     call x = 'foo(&aliased)
     return aliased
    function foo(mut x)
    version vers_a
     osr [(1==1)] (foo,vers_b,st) [mut x = &x]
     return 0
    version vers_b
     st:
     x <- 42
     return 0
  |pr} 42;

  test {pr|
    function main ()
     mut aliased = 33
     call x = 'foo(&aliased)
     return aliased
    function foo(mut x)
    version vers_a
     osr [(1==1)] (foo,vers_b,st) [mut x = x]
     return 0
    version vers_b
     st:
     x <- 42
     return 0
  |pr} 33;

  test {pr|
    function main ()
     call x = 'foo()
     return x
    function foo()
    version vers_a
     osr [(1==1)] (foo,vers_b,st) [mut x = (41 + 1)]
     return 0
    version vers_b
     mut x = 0
     st:
     return x
  |pr} 42;
  ()

let suite =
  "suite">:::
  ["mut">:: run test_mut no_input
     (has_var "x" (Value.int 2)
      &&& (trace_is Value.[int 1; int 2]));
   "decl_const">:: run test_decl_const no_input
     (has_var "x" (Value.int 1));
   "print">:: run test_print no_input
     (trace_is Value.[int 1; int 2]);
   "jump">:: run test_jump no_input
     (has_var "x" (Value.bool true));
   "jump (oo)" >:: run test_overloading no_input
     (has_var "b" (Value.bool true)
      &&& has_var "x" (Value.int 2)
      &&& has_var "y" (Value.int 1));
   "add">:: run (test_add "1" "2") no_input
     (has_var "z" (Value.int 3));
   "add2">:: run (test_add "2" "1") no_input
     (has_var "z" (Value.int 3));
   "eq">:: run (test_eq 1 2) no_input
     (has_var "z" (Value.bool false));
   "neq">:: run (test_eq 1 1) no_input
     (has_var "z" (Value.bool true));
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
   "mut_undefined">::
   (fun () -> assert_raises (Eval.Undefined_variable "n")
       (run_unchecked test_read_print_err_2
          (input [Value.bool false; Value.int 1]) ok));
   "mut_undefined2">::
   (fun () -> assert_raises (Scope.ScopeExceptionAt("main", "anon", (Scope.UninitializedVariable (VarSet.singleton "n", 3))))
       (fun() -> Scope.check_function test_read_print_err_2.main));
   "mut_undefined3">::
   (fun () -> assert_raises (Scope.ScopeExceptionAt("main", "anon", (Scope.UninitializedVariable (VarSet.singleton "b", 6))))
       (fun() -> Scope.check_function test_read_print_err_4.main));
   "scope1">:: infer_broken_scope test_broken_scope_1 (undeclared ["x"] 0);
   "scope2">:: infer_broken_scope test_broken_scope_2 (undeclared ["x"] 3);
   "scope3">:: infer_broken_scope test_broken_scope_3 (undeclared ["x"] 6);
   "scope4">:: infer_broken_scope test_broken_scope_4 (extraneous ["y"] 2);
   "scope4fixed">:: run test_broken_scope_4_fixed no_input ok;
   "scope5">:: infer_broken_scope test_broken_scope_5 (undeclared ["w"] 2);
   "scope1ok">:: run (test_scope_1 "c" "c") no_input
     (has_var "c" (Value.int 0));
   "scope1broken">:: infer_broken_scope
     (test_scope_1 "a" "c") (undeclared ["a"] 12);
   "scope1broken2">:: infer_broken_scope
     (test_scope_1 "a" "b") (undeclared ["b"; "a"] 12);
   "scope_uninitialized">:: do_test_scope_uninitialized;
   "parser">:: test_parse_disasm   ("stop 0\n");
   "parser1">:: test_parse_disasm  ("const x = 3\nprint x\nstop 0\n");
   "parser2">:: test_parse_disasm  ("goto l\nx <- 3\nl:\n");
   "parser3">:: test_parse_disasm  ("const x = (y + x)\n");
   "parser4">:: test_parse_disasm  ("x <- (x == y)\n");
   "parser5">:: test_parse_disasm  ("# asdfasdf\n");
   "parser5b">:: test_parse_disasm ("osr [(x == y)] (f, v, l) [const x = x, mut y = &x, mut v, const x = (1+2)]\nl:\n");
   "parser6">:: test_parse_disasm  ("branch (x == y) as fd\n");
   "parser7">:: test_parse_disasm  ("const x = (y + x)\n x <- (x == y)\n# asdfasdf\nbranch (x == y) as fd\n");
   "parser8">:: test_parse_disasm_file "examples/sum.sou";
   "parser_arr1">:: test_parse_disasm ("const x = array(10)\n");
   "parser_arr2">:: test_parse_disasm ("const x = []\nconst y = [1, x, nil]\n");
   "parser_arr3">:: test_parse_disasm ("const x = y[10]\n");
   "parser_arr4">:: test_parse_disasm ("const x = length(y)\n");
   "parser_arr_file">:: test_parse_disasm_file "examples/array_sum.sou";
   "disasm1">:: test_disasm_parse (test_sum 10);
   "disasm2">:: test_disasm_parse (test_add "1" "0");
   "disasm_scope1">:: test_disasm_parse test_broken_scope_4;
   "disasm_scope2">:: test_disasm_parse test_broken_scope_4_fixed;
   "disasm_scope3">:: test_disasm_parse test_broken_scope_5;
   "parser_scope1">:: test_parse_disasm "function main()\nversion active\n{a, b} print x\n{a,x,...} #asdf\n";
   "branch_pruning">:: (fun () -> test_branch_pruning_exp test_branch test_branch_pruned);
   "predecessors">:: do_test_pred;
   "branch_pruning_eval">:: (fun () -> test_branch_pruning test_branch None);
   "branch_pruning_eval2">:: (fun () -> test_branch_pruning (test_sum 10) (Some "continue"));
   "branch_pruning_eval3">:: (fun () -> test_branch_pruning test_double_loop (Some "loop_body1"));
   "reaching">:: do_test_reaching;
   "used">:: do_test_used;
   "liveness">:: do_test_liveness;
   "codemotion">:: do_test_codemotion;
   "min_lifetimes">:: do_test_minimize_lifetime;
   "constant_prop">:: do_test_const_prop_driver;
   "push_drop">:: do_test_push_drop;
   "pull_drop">:: do_test_pull_drop;
   "move_drop">:: do_test_drop_driver;
   "test_functions">:: test_functions;
   "test_mut_to_const">:: do_test_mut_to_const;
   "deopt">:: do_test_deopt;
   "array">:: do_test_array;
   ]
;;

let () =
  let test_result = run_test_tt_main suite in
  let is_success = function[@warning "-4"]
    | RSuccess _ -> true
    | _ -> false in
  if not (List.for_all is_success test_result) then exit 1;;
