#!/bin/bash

gather_generators () {
    for file in `find examples/ -name "*.ml"`; do
        ./rewrite -bench $file -domain poly > /dev/null
        ./rewrite -bench $file -domain box > /dev/null
        ./rewrite -bench $file -domain box -cover_size 128 > /dev/null
        # ./rewrite -bench $file -domain rs
    done
}

build () {
    ocamlfind ocamlopt -linkpkg -package qcheck testify_runtime.ml $1 -o bench
    ./bench
}

clean () {
    rm -f gen/*
    rm -f res.txt
}

mkdir -p gen
clean
echo "Generating benchmark"
gather_generators
cd gen
nb=$(ls *.ml | wc -l)
i=1
for file in `find . -name "*.ml"`; do
    echo -en "Running benchmark $i/$nb\r"
    ln -f ../runtime/testify_runtime.ml testify_runtime.ml
    ocamlfind ocamlopt -linkpkg -package qcheck testify_runtime.ml $file -o bench
    ./bench >> res.txt
    i=$((i+1))
done
mv res.txt ..
echo "Ouputting results in res.txt"
