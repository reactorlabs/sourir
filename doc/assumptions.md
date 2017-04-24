# Inserting Assumptions

This documents describes the rationale behind the transformations in
`Transform_assumption`.

In the following discussion we call the instruction pair composed of a
label and an osr instruction a checkpoint. For example:

```
checkpoint_2:
  osr [] (f,v,checkpoint_2) [...]
```

There are 3 primitive operations regarding assumptions:

1. Insert Checkpoints
2. Create a new Version
3. Insert an Assumption

The following assumes that all instructions belong to the function `f` and
the initial version is called `v`.

## 1. Insert Checkpoints

Before we can add assumptions to a program we need to establish the
initial relation between the different versions of the program. Initially we
achieve this by adding all possible checkpoints (they can be trimmed later).

    I   = i*
    I' := (label lᵢ ; checkpoint [] (f,v,lᵢ) Δᵢ ; i)*
    lᵢ  - fresh
    Δᵢ := { x ↤ x | ∀ x ∈ S(I', lᵢ) }
    -----------------------------------------   (init)
    I'

## 2. Create a new Version

In the most general case we have to be able to osr to the initial version.
Therefore we should always keep the baseline version untouched. But also
for intermediate steps we might wish to be able to peel off one assumption
at a time.

Creating a new version duplicates the active version and updates all osr
targets.

    (..., v ↦ I)
    I' := I[osr _ (f,_,l) _ / osr _ (f,v,l)]
           ∀   l - checkpoint label in I
    v' - fresh version label
    ------------------------------------------   (next)
    (..., v ↦ I, v' ↦ I')

## 3. Insert an Assumption

We can insert assumptions at every checkpoint

    I
    l - checkpoint label in I
    e' - valid
    I[l] = osr [e, ...] _ _
    ---------------------------------   (asm)
    I[l ↦ osr [e', e, ...] _ _]

### Example

Input program

    function main
    version v
      1: y = 1
      2: x = read
      3: branch (x=0) 4 5
      4: y = 2
      5: branch (y=x) 6 7
      6: print y
      7: stop

(init)

    function main
    version v
      1: y = 1
      2: x = read
      3: checkpoint_1:
         osr [] (main, v, checkpoint_1) [y=y, x=x]
         branch (x=0) 4 5
      4: y = 2
      5: checkpoint_2:
         osr [] (main, v, checkpoint_2) [y=y, x=x]
         branch (y=x) 6 7
      6: print y
      7: stop

(next)

    function main
    version v'
      1: y = 1
      2: x = read
      3: checkpoint_1:
         osr [] (main, v, checkpoint_1) [y=y, x=x]
         branch (x=0) 4 5
      4: y = 2
      5: checkpoint_2:
         osr [] (main, v, checkpoint_2) [y=y, x=x]
         branch (y=x) 6 7
      6: print y
      7: stop
    version v
      1: y = 1
      2: x = read
      3: checkpoint_1:
         osr [] (main, v, checkpoint_1) [y=y, x=x]
         branch (x=0) 4 5
      4: y = 2
      5: checkpoint_2:
         osr [] (main, v, checkpoint_2) [y=y, x=x]
         branch (y=x) 6 7
      6: print y
      7: stop

(asm) :  Speculate `x != 0`

    function main
    version v'
      1: y = 1
      2: x = read
      3: checkpoint_1:
         osr [x=0] (main, v, checkpoint_1) [y=y, x=x]
         branch (x=0) 4 5
      4: y = 2
      5: checkpoint_2:
         osr [] (main, v, checkpoint_2) [y=y, x=x]
         branch (y=x) 6 7
      6: print y
      7: stop
    version v
      ...

`branch (x=0)` must be false. Therefore remove the true branch.

    function main
    version v'
      1: y = 1
      2: x = read
      3: checkpoint_1:
         osr [x=0] (main, v, checkpoint_1) [y=y, x=x]
      5: checkpoint_2:
         osr [] (main, v, checkpoint_2) [y=y, x=x]
         branch (y=x) 6 7
      6: print y
      7: stop
    version v
      ...

constant folding:

    function main
    version v'
      2: x = read
      3: checkpoint_1:
         osr [x=0] (main, v, checkpoint_1) [y=1, x=x]
      5: checkpoint_2:
         osr [] (main, v, checkpoint_2) [y=1, x=x]
         branch (1=x) 6 7
      6: print 1
      7: stop
    version v
      ...

(next) + (asm) :  Speculate `x != 1`

    function main
    version v''
      2: x = read
      3: checkpoint_1:
         osr [x=0] (main, v', checkpoint_1) [y=1, x=x]
      5: checkpoint_2:
         osr [x=1] (main, v', checkpoint_2) [y=1, x=x]
         branch (1=x) 6 7
      6: print 1
      7: stop
    version v'
      2: x = read
      3: checkpoint_1:
         osr [x=0] (main, v, checkpoint_1) [y=1, x=x]
      5: checkpoint_2:
         osr [] (main, v, checkpoint_2) [y=1, x=x]
         branch (1=x) 6 7
      6: print 1
      7: stop
    version v
      ...

remove unreachable code (branch (1=x) must be false):

    function main
    version v''
      2: x = read
      3: checkpoint_1:
         osr [x=0] (main, v', checkpoint_1) [y=1, x=x]
      5: checkpoint_2:
         osr [x=1] (main, v', checkpoint_2) [y=1, x=x]
      7: stop
    version v'
      ...

hoist assumptions to the earliest possible checkpoint and remove unused checkpoints

    function main
    version v''
      2: x = read
      3: checkpoint_1:
         osr [x=0, x=1] (main, v', checkpoint_1) [y=1, x=x]
      7: stop
    version v'
      ...

