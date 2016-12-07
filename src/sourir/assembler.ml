open Sourir;;

let print_i x = (Print (Lit (Int x)))
let print   x = (Print (Var x))

let const  x i = (Decl_const (x, Lit (Int i)))
let mut    x i = (Decl_mut   (x, Lit (Int i)))

let assign x i = (Assign     (x, Lit (Int i)))

let stop      = (Stop)

let x = "x"

let assemble prog = prog


