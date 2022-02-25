executables=$(grep names dune | grep names dune | tr -d '()' | cut -d' ' -f 2-)

allowed_time="10."

if [ $# -gt 0 ]; then
    allowed_time=$1
fi


echo "\n\nALLOWED_TIME = $allowed_time sec." | tee -a log_bench.txt

for executable in $executables; do
    sed -ri "s/let allowed_time = [^in ]* in/let allowed_time = $allowed_time in/" "$executable.ml"
    dune exec "./$executable.exe" 2>/dev/null | tee -a log_bench.txt
done;
