## Simple inlining

As a simple warmup example lets consider inlining a function without
osrs. We will always assume that there is a goto-label right after the
call, and we will call it the "return label" of the call.


```
function main()
  var x = 1
  call y = 'foo(x)
  l:
  print y

function foo(var x)
  var t = nil
  read t
  branch t $z $x
  $z:
    var z = x + x
    print z
    return z
  $x:
    return x
```

The call to foo is constant and we can inline.

```
function main()
  var x = 1

  # inline prologue: create fresh names for the formals
  # and create the return variable
  var x' = x
  var y = nil
  # inline body
  var t' = nil
  read t'
  branch t' $z' $x'
  $z':
    var z' = x' + x'
    print z'
    # each return gets turned into an assignment to the return variable,
    # then a drop of all the callee variables
    # then a jump to the return label
    y <- z'
    drop t'
    drop z'
    goto l
  $x':
    y <- x'
    drop t'
    drop z'
    goto l

  # note that the scope at `l`, because we dropped caller variables,
  # is the same as in the non-inlined version
  l:
  print y
```

## Static calls

As a sidenote: If the call is not constant yet we could optimistically make it constant with the following transformation:

```
function main()
version base
  var x = 1
  var fun = someExpression
  lcall: call y = fun(x)
  lret:
  print y
```

to:

```
function main()
  var x = 1
  var fun = someExpression
  assume [fun == 'foo] else (main, base, lcall) [var x = x, var fun = fun]
  lcall: call y = 'foo(x)
  lret:
  print y
```

## With osr

Having the osr in the outer function poses no additional
difficulties. Now lets assume the inlinee has safepoints.

As an example (we use `rN` for "calle**r** labels", `eN` for
"calle**e** label", and `iN` for "**i**nlined-code" labels):

```
function main()
  version base
    r1:   var x = 1
    r2:   call y = 'foo(x)
     l:
    r3:   print y
    r4:   stop

function foo(var z)
  version base
    e1:   assume [...] else (bar, base, checkpoint) [var z = z], cont-frames
    e2:   return z
```

Not accounting for the additional stackframe the (incorrect) optimized version looks like this:

```
function main()
  version opt
    r1:  var x = 1
    r2:
        # prologue
        var z' = z
        var y = nil
    i1: assume [...] else (bar, base, checkpoint) varmap, cont-frames # wrong
    i2:
        y <- z'
        drop z'
        goto l
     l:
    r3: print y
    r4: stop
```

This is incorrect, because on bailout we would jump into (bar,
base, checkpoint) with one less frame on the stack than
previously. Before inlining, the bailout would end up with `main()`,
then `foo()`, then the frames of `cont-frames` on the stack. After
this broken inlining you would only get `main(), cont-frames`. We need
to recreate a frame for `foo()`.

A continuation frame description contains:

- the return variable `y`

- caller version (`main/base`)

- the return label `l`

- the environment at the call point (or, really, the environment
  needed after returning)

To know what the environment at the call-point is, we could decide to
only inline function calls that are followed by a checkpoint; the
call-point environment would be exactly the checkpoint
environment. But in fact we don't need this restriction; during
inlining, the current dynamic environment for each instruction iN can
always be split into two components:

- the environment of the caller, E{caller}
- the environment of the inlined code, E{inlined}N

At any label `iN`, the current environment is the disjoint union of
`E{caller}` and `E{inlined}N`. We know that `E{caller}` is unchanged during
the inlined function execution, given that those instructions come
from the callee where it is not in scope, and thus cannot modify it.

Finally, there is a substitution function `ρ` that goes from the
environment `E{callee}N` of the position `eN` of the callee into the
environment of `iN`, and more precisely its inlinee-part
`E{inlined}N` -- as `E{caller}` is not in scope in `eN`. It is not in
general an identity function, as the variables of the callee have been
renamed during inlining.

Let us consider again the bailout instruction to inline:

```
    e1:   assume [...] else (bar, base, checkpoint) varmap, cont-frames
```

The bailout mapping `map` goes from the environment `E{callee}N` to
the bailout-destination environment that we can call
`E{checkpoint}`. In the inlined position, we need to use `ρ(varmap)`
instead, that goes from `E{inlined}N` (or its extension, the
environment of `eN`) into `E{checkpoint}` as expected.

The inlined continuation frames `cont-frames` need to be updated in
the same way.

The new frame does not need to use `ρ`: it is
`(y, main/base, l, E{caller})`.

Note that we do *not* use `main/opt` as the continuation return
version, although it does contain a label `l`.

At first using `main/opt` sounds like a good idea, given that the code
after `l` in `main/opt` may be further optimized using information
made available by inlining (for example if the return value of `foo`
is statically known, it can be constant-folded after `l:`). But note
that if we bail out of `foo`, it is precisely because some of its
assumptions are invalid; we don't want to jump back into code that may
be optimized based on assumptions that we now know are incorrect.

To summarize:

```
    i1:   assume [ρ(...)] else (bar, base, checkpoint) ρ(varmap),
            (y, main/base, l, E{caller}), ρ(cont-frames)
```

Note that this is equivalent to applying the substitution to the whole
inlined instruction, `ρ(assume [...] else varmap, cont-frames)`, and
then adding the new continuation frame `(y, main/base, l, E{caller})`.
