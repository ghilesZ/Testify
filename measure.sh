#!/bin/bash

buildNrun () {
    ocamlfind ocamlopt -linkpkg -package qcheck testify_runtime.ml $1 -o bench
    ./bench
}

setup () {
    mkdir -p gen
    rm -f gen/*
    rm -f res.txt
}

generate () {
i=1
nb=`find examples/ -name "*.ml" | wc -l`
for file in `find examples/ -name "*.ml"`; do
    echo -en "\rGenerating benchmark from $nb file: $i/$nb"
    ./rewrite -bench rewritten_poly $file -domain poly > /dev/null
    ./rewrite -bench rewritten_box8 $file -domain box > /dev/null
    ./rewrite -bench rewritten_box32 $file -domain box -cover_size 32 > /dev/null
   # ./rewrite -bench $file -domain rs
    i=$((i+1))
done
echo ""
}

run () {
    cd gen
    nb=$(ls *.ml | wc -l)
    echo "$nb generator collected"
    files=`find . -name "*.ml" | sort`
    ln -f ../runtime/testify_runtime.ml testify_runtime.ml
    i=1
    for file in $files; do
        echo -en "\rRunning benchmark $i/$nb"
        buildNrun $file >> res.txt
        i=$((i+1))
    done
echo ""
}

setup
generate
run
echo "Ouputting results in gen/res.txt"
