build:
	dune build

test:
	@dune runtest --force -j 1 --no-buffer

clean:
	dune clean

.PHONY: build test clean
