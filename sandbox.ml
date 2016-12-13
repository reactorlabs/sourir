open Print
open Tests
open Batteries

let o = disassemble (drop_annots (test_sum 10))
let () = Printf.printf "%s\n" o
