#!/bin/bash

if [[ $# -eq 0 ]] ; then
    echo 'Error: was expecting some OCaml file'
    exit 0
fi
fbname=$(basename "$1" .ml)
dir="testdir_$fbname"
mkdir -p $dir
cp -f ./_build/default/.ppx/*/ppx.exe rewrite
./rewrite $1 -log > $dir/a.ml
[ ! -f log.svg ] || mv log.svg $dir/
rm -f rewrite
mv log.markdown $dir
echo "(executable (name a)(libraries testify_runtime)) " > $dir/dune
dune build $dir
