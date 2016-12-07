tests:
	ocamlbuild -I src/ -tag pkg_oUnit tests.byte
	@cp `readlink tests.byte` bin/tests.byte
	@rm tests.byte
	bin/tests.byte
	@echo

main:
	ocamlbuild -I src/ main.byte
	@cp `readlink main.byte` bin/main.byte
	@rm main.byte

clean:
	-rm -rf _build/ bin/*

.PHONY: tests clean

