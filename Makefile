BIN=rewrite

all:
	@dune build

$(BIN): all
	@cp ./_build/default/.ppx/*/ppx.exe $@

test:
	@dune runtest --force -j 1 --no-buffer

clean:
	@rm -f $(BIN)
	@dune clean

.PHONY: build test clean
