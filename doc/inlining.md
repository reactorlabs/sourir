## Warmup

As a simple warmup example lets consider inlining a function without osrs.
Using some fresh variables for all variables of the function we simulate a letrec
block to evaluate the body inside.

```
function main()
  var x = 1
  call y = 'foo(x)
  print y

function foo(var x)
  return x
```

The call to foo is constant and we can inline.

```
function main()
  var x = 1

  #inline prologue: create fresh names
  var x_1 = x
  # inline body
  var res = x_1
  goto inline_epilogue:
  # epilogue
  inline_epiloque:
  drop x_1
  var y = res
  drop res

  print y
```

## Static calls

As a sidenote: If the call is not constant yet we could optimistically make it constant with the following transformation:

```
function main()
  var x = 1
  var call = someExpression
  call y = call(x)
  print y
```

to:

```
function main()
  var x = 1
  var call = someExpression
  osr [call != 'foo] ...
  call y = 'foo(x)
  print y
```

## With osr

Having the osr in the outer function poses no additional difficulties. Now lets assume the inlinee has safepoints.
As an example:

```
function main()
  version base
    1   var x = 1
    2   call y = 'foo(x)
    3   osr sp1 [] (main, base, sp1) [var x = x, var y = y]
    4   print y

function foo(var z)
  version base
    1   osr sp2 [] (foo, base, sp2) [var z = z]
    2   return z
```

The safepoints of the inlinee need to be extended to recreate the correct number of stack frames.
Not accounting for the additional stackframe the (incorrect) optimized version looks like this:

```
function main()
  version opt
    1   var x = 1
    2a  var z_1 = x
    2b  osr sp2 [] (foo, base, sp2) [var z = z_1]   # wrong
    2c  var y = z_1
    2d  drop x_1
    3   osr sp1 [] (main, base, sp1) [var x = x, var y = y]
    4   print y
  ...

function foo(var z)
  version base
    1   osr sp2 [] (foo, base, sp2) [var z = z]
    2   return z
```

For the recreation of the stack to work the precise stacklayout of the caller needs to be known after the inlinee returns (ie. there must be an osr right after the call).
The combined osr is supposed to push the continuation for the call to foo.

```
    2b  osr sp2 [] (foo, base, sp2) [var z = z_1],
                   (main, base, sp1) [var y = $, var x = x]
```

The special $ register specifies the target binding for the continuation.

Remember the following defs from the semantic:

    C ::= (a, E, I, l)                 continuation:  result accumulator, environment, instructions, label
    M ::= (P, C*) : (I, T, H, E, l)    machine state: program, continuations : instructions, trace, heap, environment, pc

Before the safepoint `sp2` our machine state is:

    (P, ())                          :  (main::opt, T, H, {x=1, z_1=1}, 2b)

If the osr fires the next state would be:

    (P, (y, {x=1}, main::base, sp1)) :  (foo::base, T, H, {z=1},         1)

After the function foo returns it is:

    (P, ())                          :  (main::base, T, H, {x=1, y=1},   3)
