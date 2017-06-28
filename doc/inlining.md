## Simple inlining

As a simple warmup example lets consider inlining a function without osrs.


```
function main()
  var x = 1
  call y = 'foo(x) -> l
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

(the `-> l` syntax indicates that `l` is the "return label" of the
call; it is a goto-label such that jumping to it goes to the next
instruction after the call.)

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
  # epilogue: return label
  l:

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
  assume [call == 'foo] or ...
  call y = 'foo(x)
  print y
```

## With osr

Having the osr in the outer function poses no additional
difficulties. Now lets assume the inlinee has safepoints.

As an example (we use `rN` for calleR labels, `eN` for calleE label,
and `iN` for Inlined-code labels):

```
function main()
  version base
    r1:   var x = 1
    r2:   call y = 'foo(x) -> l
    r3:   print y
    r4:   stop

function foo(var z)
  version base
    e1:   assume [...] or (bar, base, checkpoint) [var z = z], cont-frames
    e2:   return z
```

Not accounting for the additional stackframe the (incorrect) optimized version looks like this:

```
function main()
  version opt
        var x = 1
        # prologue
        var z' = z
        var y = nil
    i1: assume [...] or (bar, base, checkpoint) varmap, cont-frames # wrong
    i2:
        y <- z'
        drop z'
        goto l
    l:
        print y
```

This is incorrect, because we would jump into (bar, base, checkpoint)
with one less frame on the stack than previously. Before inlining, the
bailout would end up with `main()`, then `foo()`, then the frames of
`cont-frames` on the stack. After this broken inlining you would only
get `main(), cont-frames`. We need to recreate a frame for `foo()`.

A continuation frame description contains:

- the return variable `y`

- caller version (`main/base`)

- the return label label `l`, which will be turned into a return pc
  when building the frame at runtime

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
    e1:   assume [...] or (bar, base, checkpoint) varmap, cont-frames
```

The bailout mapping `map` goes from the environment `E{callee}N` to
the bailout-destination environment that we can call
`E{checkpoint}`. In the inlined position, we need to use `ρ(varmap)`
instead (applying `ρ` to every right-hand-side of `varmap`), that goes
from `E{inlined}N` (or its extension, the environment of `eN`) into
`E{checkpoint}` as expected.

The continuation frames need to be updated in the same way.

The new continuation frame is `(y, main/base, l, E{caller})`.

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
    i1:   assume [ρ(...)] or (bar, base, checkpoint) ρ(varmap),
            (y, main/base, l, E{caller}), ρ(cont-frames)
```
