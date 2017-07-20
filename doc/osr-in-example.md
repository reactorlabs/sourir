## Osr-in example

The osr-in trace as we discussed would look somewhat like that:

```
F(n):

# base, unoptimized version remains active
base (active):
  start:
    call fast = read_config()
    var k = 0
  loop: branch (k < n) $continue $end
  $continue:
    k <- (k + 1)
    branch fast $fast $slow
  $fast:
    ...
    goto loop
  $slow:
    ...
    goto loop
  $end: ...

run-in-which-the-profiler-kicked-in:
  start:
    call fast = read_config()
    assume [false] (F.optimized.osr-in) [fast = true]
    # the profiler kicked in above, you can ignore the rest
  loop: branch (k < n) $continue $end
  $continue:
    k <- (k + 1)
    branch fast $fast $slow
  $fast:
    ...
    goto loop
  $slow:
    ...
    goto loop
  $end: ...

# this is the part that is executed if you start from the version that osred-in
optimized:
    # this version is *not* active and never called from base;
    # it is only an incomplete continuation
    # this environment assignment was generated from the actual run
    # during which the profiler kicked in
    var fast = true
  osr-in:
  loop: branch (k < n) $continue $end
  $continue:
    k <- (k + 1)
    ... # fast path only
    goto loop
  $end: ...
```

## Alternative (current) approach

Question: what is the advantage compared to:

```
F(n):
optimized (active):
  start:
    call fast = read_config()
    var k = 0
    assume [fast] (F.base.loop) [fast = fast]
  loop: branch (k < n) $continue $end
  $continue:
    k <- (k + 1)
    ... # fast path only
  $end: ...

base:
  start:
    call fast = read_config()
    var k = 0
  loop: branch (k < n) $continue $end
  $continue:
    k <- (k + 1)
    branch fast $fast $slow
  $fast:
    ...
    goto loop
  $slow:
    ...
    goto loop
  $end: ...
```

In this second approach, the story is that the profiler, after
executing `base` many times and noticing that we always had
`fast = true`, decided to create an `optimized` copy of the code with
a new checkpoint, optimized it, and made it the active version.




## Complete story?

Maybe the complete story is like this: the profiler kicks in *during*
the execution of the base version, so the base version is replaced by
an optimized active version (as in the current approach) *and*
modified to osr-in to a continuation for the current call (which may
be long). For example, maybe the osr-in happened within the loop.

```
F(n):
optimized (active):
  start:
    call fast = read_config()
    var k = 0
    assume [fast] (F.base.loop) [fast = fast]
  loop: branch (k < n) $continue $end
  $continue:
    k <- (k + 1)
    ... # fast path only
  $end: ...

base:
  start:
    call fast = read_config()
    var k = 0
  loop: branch (k < n) $continue $end
  $continue:
    k <- (k + 1)
    assume [false] <F.continuation.osr-in> [fast = true, k = 42, n = 4242]
    # this (above) is where osr-in happened
    branch fast $fast $slow
  $fast:
    ...
    goto loop
  $slow:
    ...
    goto loop
  $end: ...

continuation:
    # this version is *not* active and never reached from the active version;
    # it is only an incomplete continuation jumped-in from `base`
    # this environment assignment was generated from the actual run
    # during which the profiler kicked in
    var k = 42
    # the assignments `var fast = true` and `n <- 4242` were optimized away
  osr-in:
  loop: branch (k < 4242) $continue $end
  $continue:
    k <- (k + 1)
    ... # fast path only
    goto loop
  $end: ...
```
