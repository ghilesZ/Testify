#!/bin/bash

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
i=1
echo "Generating benchmark"
nb=`find examples/ -name "*.ml" | wc -l`
for file in `find examples/ -name "*.ml"`; do
    echo -en "generating benchmark $i/$nb\r"
    ./rewrite -bench rewritten_${i}_poly $file -domain poly > /dev/null
    ./rewrite -bench rewritten_${i}_box8 $file -domain box > /dev/null
    ./rewrite -bench rewritten_${i}_box32 $file -domain box -cover_size 32 > /dev/null
   # ./rewrite -bench $file -domain rs
    i=$((i+1))
done
echo "Generation done"
cd gen
nb=$(ls *.ml | wc -l)
i=1
for file in `find . -name "*.ml" | sort`; do
    echo -en "Running benchmark $i/$nb\r"
    ln -f ../runtime/testify_runtime.ml testify_runtime.ml
    ocamlfind ocamlopt -linkpkg -package qcheck testify_runtime.ml $file -o bench
    ./bench >> res.txt
    i=$((i+1))
done
mv res.txt ..
echo "Ouputting results in res.txt"
