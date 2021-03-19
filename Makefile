build:
	@echo 'You can run the following to set a "rewrite" command for launching testify on a .ml file'
	@echo 'alias rewrite="./_build/default/.ppx/$$(ls _build/default/.ppx)/ppx.exe"'
	dune build
	@echo

test:
	@dune runtest --force -j 1 --no-buffer

clean:
	dune clean

.PHONY: build test clean
