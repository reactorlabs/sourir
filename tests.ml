open OUnit
open Instr
open Eval
open Scope

let ok _ = true

let trace_is li =
  fun conf -> read_trace conf = li
let has_var x v =
  fun conf -> (lookup conf.heap conf.env x = v)

let (&&&) p1 p2 conf = (p1 conf) && (p2 conf)

let run prog pred () =
  let final_conf = run_forever prog in
  assert (pred final_conf)

let run_checked prog pred =
  let () = ignore (infer prog) in
  run prog pred

let test_print =
  let open Assembler.OO in
  Assembler.assemble [|
    print (int 1);
    print (int 2);
    stop
  |]

let test_decl_const =
  let open Assembler.OO in
  let x = int_var "x" in
  Assembler.assemble [|
    const x (int 1);
    print x;
    stop;
  |]

let test_mut =
  let open Assembler.OO in
  let x = int_var "x" in
  Assembler.assemble [|
    mut x (int 1);
    print x;
    assign x (int 2);
    print x;
    stop;
  |]

let test_jump =
  let open Assembler.OO in
  let x = int_var "x" in
  Assembler.assemble [|
    mut x (bool true);
    goto "jump";
    assign x (bool false);
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
    stop;
  |]

let test_add a b =
  let open Assembler.OO in
  let x, y, z = int_var "x", int_var "y", int_var "z" in
  Assembler.assemble [|
    mut x (int a);
    mut y (int b);
    add z x y;
  |]

let test_eq a b =
  let open Assembler.OO in
  let x, y, z = int_var "x", int_var "y", bool_var "z" in
  Assembler.assemble [|
    mut x (int a);
    mut y (int b);
    eq z x y;
  |]

let test_sum limit_ =
  let open Assembler.OO in
  let ax, i, sum, limit, one =
    bool_var "ax", int_var "i", int_var "sum", int_var "limit", int_var "one" in
  Assembler.assemble [|
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
  Assembler.assemble [|
    print x;
  |]

let test_broken_scope_2 =
  let open Assembler.OO in
  let x = int_var "x" in
  Assembler.assemble [|
    goto "l";
    const x (int 0);
    label "l";
    print x;
  |]

let test_broken_scope_3 =
  let open Assembler.OO in
  let x, y = int_var "x", int_var "y" in
  Assembler.assemble [|
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
  Assembler.assemble [|
    const y (bool false);
    branch y "cont" "next";
    label "next";
    const x (int 0);
    label "cont";
    print x;
  |]

let test_scope_1 test_var1 test_var2 =
  let open Assembler.OO in
  let a, b, c, t = int_var "a", int_var "b", int_var "c", bool_var "t" in
  Assembler.assemble [|
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

let infer_broken_scope program missing_vars = function() ->
     let test = function() -> ignore (infer program) in
     let expected = (UndefinedVariable (VarSet.of_list missing_vars)) in
     assert_raises expected test

let suite =
  let open Assembler in
  "suite">:::
  ["mut">:: run_checked test_mut
     (has_var "x" (Value.int 2)
      &&& (trace_is Value.[int 1; int 2]));
   "decl_const">:: run_checked test_decl_const
     (has_var "x" (Value.int 1));
   "print">:: run_checked test_print
     (trace_is Value.[int 1; int 2]);
   "jump">:: run_checked test_jump (has_var "x" (Value.bool true));
   "jump (oo)" >:: run_checked test_overloading
     (has_var "b" (Value.bool true)
      &&& has_var "x" (Value.int 2)
      &&& has_var "y" (Value.int 1));
   "add">:: run_checked (test_add 1 2) (has_var "z" (Value.int 3));
   "add2">:: run_checked (test_add 2 1) (has_var "z" (Value.int 3));
   "eq">:: run_checked (test_eq 1 2) (has_var "z" (Value.bool false));
   "neq">:: run_checked (test_eq 1 1) (has_var "z" (Value.bool true));
   "loops">:: run_checked (test_sum 5) (has_var "sum" (Value.int 10));
   "scope1">:: infer_broken_scope test_broken_scope_1 ["x"];
   "scope2">:: infer_broken_scope test_broken_scope_2 ["x"];
   "scope3">:: infer_broken_scope test_broken_scope_3 ["x"];
   "scope3run">:: run test_broken_scope_3 (has_var "x" (Value.int 0));
   "scope4ok">:: run_checked (test_scope_1 "c" "c") (has_var "c" (Value.int 0));
   "scope4broken">:: infer_broken_scope (test_scope_1 "a" "c") ["a"];
   "scope4broken2">:: infer_broken_scope (test_scope_1 "a" "b") ["b"; "a"];
  ]
;;

let _ =
  run_test_tt_main suite;
;;
