# CC   = ocamlfind ocamlc
# EXE  = test
# PPX  = preprocess
# LIBS = compiler-libs.common

# all: exe

# test: exe
# 	./$(EXE)

# exe: ppx
# 	$(CC) test.ml -ppx "./$(PPX) -as-ppx" -o $(EXE) -linkpkg -package zarith

# ppx:
# 	$(CC) -package ppx_tools.metaquot ppx_wideopen.ml -linkpkg -package $(LIBS) -o $(PPX)

# clean:
# 	rm -f `find . -name "*.o"`
# 	rm -f `find . -name "*.a"`
# 	rm -f `find . -name "*.cm*"`
# 	rm -f `find . -name "*~"`
# 	rm -f `find . -name "\#*"`
# 	rm -f $(PPX) $(EXE)

build:
	dune build

test:
	@dune runtest

clean:
	dune clean

.PHONY: build test clean
