BIN=rewrite

all:
	@dune build
	@$(MAKE) -s $(BIN)

$(BIN):
	@cp ./_build/default/.ppx/*/ppx.exe $@

test:
	@dune runtest --force -j 1 --no-buffer

clean:
	@rm -f $(BIN)
	@rm -f *.log
	@dune clean

.PHONY: build test clean $(BIN)
