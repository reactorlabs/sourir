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
	utop -I _build sourir.cma

run: sourir
	./sourir test.sou


sb:
	$(OCAMLBUILD) sandbox.byte
	_build/sandbox.byte

clean:
	ocamlbuild -clean

.PHONY: all run tests clean sourir sb

