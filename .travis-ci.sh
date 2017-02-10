eval `opam config env`
make install-deps
make sourir
make tests && make test_examples
