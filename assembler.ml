open Ast
open Eval

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


module OO = struct
  type 'a litteral = <
    eval : 'a;
    litteral : Ast.litteral;
    value : value;
    expression : expression;
  >

  type 'a value = <
    eval : 'a;
    value : Ast.value;
    expression : expression;
  >

  type 'a variable = <
    eval : Eval.heap -> Eval.environment -> 'a;
    variable : Ast.variable;
    expression : expression;
  >

  type 'a expression = <
    eval : Eval.heap -> Eval.environment -> 'a;
    expression : Ast.expression;
  >

  let var of_value v : 'a variable = object
    method eval heap env = of_value (lookup heap env v)
    method variable = v
    method expression = Var v
  end

  let bool_var = var get_bool
  let int_var = var get_int

  let int n : int litteral = object
    method eval = n
    method litteral : Ast.litteral = Int n
    method value : Ast.value = Lit (Int n)
    method expression : Ast.expression = Lit (Int n)
  end

  let bool b : bool litteral = object
    method eval = b
    method litteral : Ast.litteral = Bool b
    method value : Ast.value = Lit (Bool b)
    method expression : Ast.expression = Lit (Bool b)
  end

  let const x e = Decl_const (x#variable, e#expression)
  let mut x e = Decl_mut (x#variable, e#expression)
  let assign x e = Assign (x#variable, e#expression)
  let print e = Print (e#expression)
  let goto l = Goto l
  let label l = Label l
end
