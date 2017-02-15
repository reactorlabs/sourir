OCAMLBUILD=ocamlbuild -use-ocamlfind -use-menhir -no-links
# -use-ocamlfind: use the ocamlfind library manager
# -use-menhir: use the Menhir parser generator
# -no-links: do not create symlink from build outputs in _build into
#            the project directory

all: tests sourir
	rm -rf $(TEMPDIR)

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

TEMPDIR := $(shell mktemp -d)

test_examples: sourir
	mkdir $(TEMPDIR)/examples
	for f in examples/*.sou; do yes 0 | ./sourir $$f --quiet                   > $(TEMPDIR)/$$f.out; done
	for f in examples/*.sou; do yes 0 | ./sourir $$f --quiet --cm --prune      > $(TEMPDIR)/$$f.opt.out && diff $(TEMPDIR)/$$f.out $(TEMPDIR)/$$f.opt.out; done
	for f in examples/*.sou; do yes 1 | ./sourir $$f --quiet                   > $(TEMPDIR)/$$f.out; done
	for f in examples/*.sou; do yes 1 | ./sourir $$f --quiet --cm --prune      > $(TEMPDIR)/$$f.opt.out && diff $(TEMPDIR)/$$f.out $(TEMPDIR)/$$f.opt.out; done
	rm -rf $(TEMPDIR)

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
