# sourir

sourir is cuter than [RIR](https://github.com/reactorlabs/rir)

## Howto

Install [Opam](https://opam.ocaml.org/doc/Install.html)

    opam install ocaml.4.04.0
    # FIXME: install dependencied
    git clone https://github.com/reactorlabs/sourir
    cd sourir
    make sourir
    ./sourir test.sou

## Syntax / Semantics

The language is still in flux and there is no written syntax or semantics. See
parser.mly or the testcases in tests.ml to get an idea of the syntax. See
Eval.reduce for the operational semantics.

## Hacking

Requirements

    # FIXME

Add tests and run them with

    make tests

Run a toplevel utop with

    make runtop

Send new code by pull-request
