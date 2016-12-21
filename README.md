# sourir

sourir is cuter than [RIR](https://github.com/reactorlabs/rir)

## Howto

Install [Opam](https://opam.ocaml.org/doc/Install.html), the OCaml
package manager, and then:

    opam install ocaml.4.04.0
    git clone https://github.com/reactorlabs/sourir
    cd sourir
    make install-deps
    make sourir
    ./sourir examples/sum.sou

## Syntax / Semantics

The language is still in flux. See [parser.mly](parser.mly) to get an
idea of the syntax, and [eval.ml](eval.ml), in particular
`Eval.reduce`, for the operational semantics.

## Hacking

Add tests and run them with

    make tests

Run a toplevel utop with

    make runtop

Send new code by pull-request
