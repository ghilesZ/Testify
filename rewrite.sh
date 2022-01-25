#!/bin/sh

set -euC

if [ $# -eq 0 ]; then
    echo 'Error: was expecting some OCaml file'
    exit 1
fi
fbname=$(basename "$1" .ml)
dir="testdir_$fbname"
mkdir -p "$dir"
rm -f "$dir/a.ml"
dune exec src/rewriter.exe -- "$1" -log > "$dir/a.ml"
[ ! -f log.svg ] || mv log.svg "$dir"/
mv log.markdown "$dir"
echo "(executable (name a)(libraries testify_runtime)) " > "$dir/dune"
dune build "$dir"
