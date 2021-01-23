build:
	dune build

test:
	@dune runtest -f -j 1 --no-buffer

clean:
	dune clean

.PHONY: build test clean
