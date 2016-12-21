open Instr
open Eval

module Value = struct
  let int n : value = Lit (Int n)
  let bool b : value = Lit (Bool b)
end

let assemble prog = prog

module OO = struct
  type 'a litteral = <
    eval : 'a;
    litteral : Instr.litteral;
    value : value;
    simple_expression : simple_expression;
    expression : expression;
  >

  type 'a value = <
    eval : 'a;
    value : Instr.value;
    simple_expression : simple_expression;
    expression : expression;
  >

  type 'a variable = <
    eval : Eval.heap -> Eval.environment -> 'a;
    variable : Instr.variable;
    simple_expression : simple_expression;
    expression : expression;
  >

  type 'a expression = <
    eval : Eval.heap -> Eval.environment -> 'a;
    expression : Instr.expression;
  >

  let var of_value v : 'a variable = object
    method eval heap env = of_value (lookup heap env v)
    method variable = v
    method simple_expression = Var v
    method expression = Simple (Var v)
  end

  let bool_var = var get_bool
  let int_var = var get_int

  let int n : int litteral = object
    method eval = n
    method litteral : Instr.litteral = Int n
    method value : Instr.value = Lit (Int n)
    method simple_expression : Instr.simple_expression = Lit (Int n)
    method expression : Instr.expression = Simple (Lit (Int n))
  end

  let bool b : bool litteral = object
    method eval = b
    method litteral : Instr.litteral = Bool b
    method value : Instr.value = Lit (Bool b)
    method simple_expression : Instr.simple_expression = Lit (Bool b)
    method expression : Instr.expression = Simple (Lit (Bool b))
  end

  let op_add x1 x2 = object
    method expression = (Op (Plus, [x1#simple_expression; x2#simple_expression]))
  end

  let op_eq x1 x2 = object
    method expression = (Op (Eq, [x1#simple_expression; x2#simple_expression]))
  end

  let const x e = Decl_const (x#variable, e#expression)
  let mut x e = Decl_mut (x#variable, e#expression)
  let assign x e = Assign (x#variable, e#expression)
  let read x = Read (x#variable)
  let print e = Print (e#expression)
  let goto l = Goto l
  let branch e tr fs = Branch (e#expression, tr, fs)
  let label l = Label l
  let stop = (Stop)

  let add r a b = mut r (op_add a b)
  let eq  r a b = mut r (op_eq a b)
end
