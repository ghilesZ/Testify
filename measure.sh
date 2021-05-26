#!/bin/bash

declare -A CONF

CONF["poly"]="-domain poly"
CONF["box08"]="-domain box -cover_size 8"
CONF["box64"]="-domain box -cover_size 64"
CONF["rs"]="-domain rs"

setup () {
    mkdir -p gen
    rm -f gen/*
}

buildNrun () {
    ocamlfind ocamlopt -linkpkg -package qcheck testify_runtime.ml $1 -o bench
    ./bench
}

run () {
    cd gen
    files=`find . -name "*.ml" | sort`
    nbfiles=`find . -name "*.ml" | wc -l`
    ln -f ../runtime/testify_runtime.ml testify_runtime.ml
    i=1
    echo "location kind var domain rate mu" >> $1db
    for file in $files; do
        echo -en "\rSpeed estimation for generator $i/$nbfiles"
        buildNrun $file >> $1db
        i=$((i+1))
    done
    echo ""
    echo "Ouputting results for $1 in gen/$1db"
    rm -f *.ml
    rm -f *.o
    cd ..
}

generate () {
    nb=`find examples/ -name "*.ml" | wc -l`
    echo "Building generators from $nb files"
    for conf in ${!CONF[@]}; do
        i=1
        echo "Benchmarking for configuration: $conf"
        for file in `find examples/ -name "*.ml"`; do
            echo -en "\r$i/$nb"
            ./rewrite -bench $conf ${CONF[${conf}]} $file > /dev/null
            i=$((i+1))
        done
        nbgen=$(ls gen/*.ml 2>/dev/null | wc -l)
        echo -e "\n$nbgen generator collected"
        run $conf
    done
}

format () {
    cd gen
    q -H "SELECT kind,var FROM box08db GROUP BY location,domain" > tmp
    arr=(box08 box64 poly rs)
    for conf in ${arr[@]}; do
        q -H "SELECT rate,mu FROM ${conf}db GROUP BY location,domain" > tmp$conf
        mv tmp tmp2
        paste -d " " tmp2 tmp$conf > tmp
    done
    sed -e "s/ / \& /g" < tmp > tmp2
    sed 's/$/\\\\ \\hline/g' < tmp2 > table.tex
    echo "formatting results in gen/table.tex"
}

setup; generate; format
