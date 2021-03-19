build:
	dune build
	@echo
	@echo 'You can type the following to set a "rewrite" command for running testify on a .ml file'
	@echo 'alias rewrite="./_build/default/.ppx/$$(ls _build/default/.ppx)/ppx.exe"'

test:
	@dune runtest --force -j 1 --no-buffer

clean:
	dune clean

.PHONY: build test clean
