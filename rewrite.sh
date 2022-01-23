#!/bin/bash

fbname=$(basename "$1" .ml)
dir="testdir_$fbname"
mkdir -p $dir
cp -f ./_build/default/.ppx/*/ppx.exe rewrite
./rewrite $1 -log > $dir/a.ml
rm -f rewrite
mv log.markdown $dir
echo "(executable (name a)(libraries testify_runtime)) " > $dir/dune
dune build $dir
