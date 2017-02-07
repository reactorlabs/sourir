OCAMLBUILD=ocamlbuild -use-ocamlfind -use-menhir -no-links
# -use-ocamlfind: use the ocamlfind library manager
# -use-menhir: use the Menhir parser generator
# -no-links: do not create symlink from build outputs in _build into
#            the project directory

all: tests sourir

tests:
	$(OCAMLBUILD) tests.byte
	_build/tests.byte

sourir:
	$(OCAMLBUILD) sourir.byte
	cp _build/sourir.byte sourir

lib:
	$(OCAMLBUILD) sourir.cma

runtop: lib
	utop -require menhirLib -I _build sourir.cma

run: sourir
	./sourir examples/sum.sou

test_examples: sourir
	for f in examples/*.sou; do yes 0 | ./sourir $$f > /dev/null; done
	for f in examples/*.sou; do echo $$f; yes 0 | ./sourir $$f --prune > /dev/null; done

clean:
	ocamlbuild -clean

# The parser.messages file is maintained semi-automatically: a human
# should maintain the error messages, but the parser generators update
# the error state numbers and the example of token inputs that lead to
# those. After changing the parser you should manually build this
# target and inspect the change to the .messages file; if a new error
# state appears, you should add an error message for it.
update-parser-messages:
	ocamlbuild parser.messages.update
	cp _build/parser.messages parser.messages

install-deps:
	opam pin add sourir . --no-action # tell opam about a local "sourir" package
	opam install --deps-only sourir # then install its dependencies

.PHONY: all run tests clean sourir test_examples

