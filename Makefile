OCAMLBUILD=ocamlbuild -cflag -g

# use the ocamlfind library manager
OCAMLBUILD+= -use-ocamlfind

# use the Menhir parser generator
OCAMLBUILD+= -use-menhir

# do not create symlink from build outputs in _build
# into the project directory
OCAMLBUILD+= -no-links

# Bisect ocamlbuild plugin for coverage analysis
OCAMLBUILD+= -plugin-tag 'package(bisect_ppx.ocamlbuild)'

all: tests test_examples sourir

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
	bash test_examples.sh

test_examples_long: sourir
	bash test_examples.sh --long

clean:
	ocamlbuild -clean

# bisect-ppx coverage machinery

COVERAGE_DIR=_build/_coverage
COVERAGE_TARGETS=tests test_examples

coverage-run:
	mkdir -p $(COVERAGE_DIR)
	$(MAKE) \
	  BISECT_COVERAGE=YES \
	  BISECT_FILE=$(shell pwd)/$(COVERAGE_DIR)/bisect \
	  $(COVERAGE_TARGETS)

coverage-report:
	bisect-ppx-report -I _build $(COVERAGE_DIR)/*.out -html $(COVERAGE_DIR)/report
	@echo summary
	@bisect-ppx-report -I _build $(COVERAGE_DIR)/*.out -text -
	@echo
	@echo see $(COVERAGE_DIR)/report/index.html for more details

coverage:
	$(MAKE) coverage-run
	$(MAKE) coverage-report

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

.PHONY: all run tests clean sourir test_examples coverage-run coverage-report
