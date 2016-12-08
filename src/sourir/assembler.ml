open Sourir;;

module Value = struct
  let int n : value = Lit (Int n)
  let bool b : value = Lit (Bool b)
end

let assemble prog = prog

module OO = struct
  type 'a litteral = <
    eval : 'a;
    litteral : Sourir.litteral;
    value : value;
    expression : expression;
  >

  type 'a value = <
    eval : 'a;
    value : Sourir.value;
    expression : expression;
  >

  type 'a variable = <
    eval : Sourir.heap -> Sourir.environment -> 'a;
    variable : Sourir.variable;
    expression : expression;
  >

  type 'a expression = <
    eval : Sourir.heap -> Sourir.environment -> 'a;
    expression : Sourir.expression;
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
    method litteral : Sourir.litteral = Int n
    method value : Sourir.value = Lit (Int n)
    method expression : Sourir.expression = Lit (Int n)
  end

  let bool b : bool litteral = object
    method eval = b
    method litteral : Sourir.litteral = Bool b
    method value : Sourir.value = Lit (Bool b)
    method expression : Sourir.expression = Lit (Bool b)
  end

  let op_add x1 x2 = object
    method expression = (Op (Plus, [x1#variable; x2#variable]))
  end

  let op_eq x1 x2 = object
    method expression = (Op (Eq, [x1#variable; x2#variable]))
  end

  let const x e = Decl_const (x#variable, e#expression)
  let mut x e = Decl_mut (x#variable, e#expression)
  let assign x e = Assign (x#variable, e#expression)
  let print e = Print (e#expression)
  let goto l = Goto l
  let branch e tr fs = Branch (e#expression, tr, fs)
  let label l = Label l
  let stop = (Stop)

  let add r a b = mut r (op_add a b)
  let eq  r a b = mut r (op_eq a b)
end
