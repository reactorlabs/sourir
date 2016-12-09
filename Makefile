tests:
	ocamlbuild -use-ocamlfind -no-links tests.byte
	_build/tests.byte
	@echo

sourir:
	ocamlbuild -use-ocamlfind -use-menhir -no-links sourir.byte
	cp _build/sourir.byte sourir

run: sourir
	./sourir test.sou

clean:
	ocamlbuild -clean

.PHONY: tests clean

