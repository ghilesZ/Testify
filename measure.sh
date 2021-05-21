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
    ./rewrite -bench reject $file -domain rs > /dev/null
    ./rewrite -bench poly $file -domain poly > /dev/null
    ./rewrite -bench box08 $file -domain box > /dev/null
    ./rewrite -bench box32 $file -domain box -cover_size 32 > /dev/null
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
    echo "location domain rate mu" >> res.txt
    for file in $files; do
        echo -en "\rSpeed estimation for generator $i/$nb"
        buildNrun $file >> res.txt
        i=$((i+1))
    done
    echo ""
    echo "Ouputting results in gen/res.txt"
}

format () {
    q -H "SELECT location,domain,rate,mu FROM res.txt GROUP BY location,domain" > table.tex
    echo "formatting results in gen/table.tex"
}

setup
generate
run
format
