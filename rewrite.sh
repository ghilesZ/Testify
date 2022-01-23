#!/bin/bash

fbname=$(basename "$1" .ml)
dir="testdir_$fbname"
mkdir -p $dir
cp -f ./_build/default/.ppx/*/ppx.exe rewrite
./rewrite $1 > $dir/a.ml
rm -f rewrite
echo "(executable (name a)(libraries testify_runtime)) " > $dir/dune
dune build $dir
