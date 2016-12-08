open Sourir;;

module Value = struct
  let int n : value = Lit (Int n)
  let bool b : value = Lit (Bool b)
end

module Instr = struct
  let print_i x = (Print (Lit (Int x)))
  let print   x = (Print (Var x))

  let const  x i = (Decl_const (x, Lit (Int i)))
  let mut_b  x b = (Decl_mut   (x, Lit (Bool b)))
  let mut_i  x i = (Decl_mut   (x, Lit (Int i)))

  let assign x i = (Assign     (x, Lit (Int i)))
  let assign_b x b = (Assign   (x, Lit (Bool b)))

  let branch x l1 l2 = (Branch (x, l1, l2))

  let label l = (Label l)
  let goto l = (Goto l)

  let stop      = (Stop)
end

let x = "x"

let assemble prog = prog
