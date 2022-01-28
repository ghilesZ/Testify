all:
	@dune build examples/ src/rewriter.exe # dont build test_dir*

test:
	@dune runtest --force -j1 --no-buffer

clean:
	@rm -f *.log
	@dune clean
	@rm -f *.markdown
	@rm -rf testdir_*

.PHONY: build test clean
