BIN=rewrite

all:
	@dune build

test:
	@dune runtest --force -j1 --no-buffer

clean:
	@rm -f $(BIN)
	@rm -f *.log
	@dune clean
	@rm -f *.markdown
	@rm -rf testdir_*

.PHONY: build test clean $(BIN)
