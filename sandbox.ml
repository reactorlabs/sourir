open Print
open Tests
open Batteries

let o = disassemble (test_sum 10)
let () = Printf.printf "%s\n" o
