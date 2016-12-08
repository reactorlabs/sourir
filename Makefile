tests:
	ocamlbuild -use-ocamlfind -no-links tests.byte
	_build/tests.byte
	@echo

clean:
	ocamlbuild -clean

.PHONY: tests clean

