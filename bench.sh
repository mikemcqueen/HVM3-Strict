#!/bin/bash

num_iters=20

if [ $# -gt 0 ]; then
  num_iters="$1"
fi

cleanup() {
    echo "Caught CTRL+C, cleaning up..."
    pkill -P $$      # Kill all child processes of this script
    exit 1
}

trap cleanup SIGINT

cmd="cabal run . -- run examples/bench_parallel_sum_range.hvms -s"

total_mips=0
min_mips=999999999
max_mips=0
first_itrs=0
outfile=out

echo "Running $cmd for $num_iters iterations..."

for (( i=1; i<=$num_iters; i++ )); do
    output=$($cmd 2>$outfile)
    
    mips=$(echo "$output" | grep "MIPS:" | awk '{print $2}')
    itrs=$(echo "$output" | grep "ITRS:" | awk '{print $2}')
    size=$(echo "$output" | grep "SIZE:" | awk '{print $2}')
    
    [[ -z "$itrs" ]] && err=1 || err=0

    if (( !err )) && [[ $first_itrs == 0 ]]; then
        first_itrs="$itrs"
    elif (( err )) || [[ $first_itrs != $itrs ]]; then
        if (( err )); then
            echo "ERROR @ $i: missing ITRS"
        else
            echo "ERROR @ $i: ITRS: $itrs mismatch with first ITRS: $first_itrs"
        fi
        echo "Output:"
        echo "$output"
        echo "------"
        echo "tail out:"
        tail "$outfile"
        exit 1
    fi

    if [[ $mips < $min_mips ]]; then
        min_mips="$mips"
    fi
    
    if [[ $mips > $max_mips ]]; then
        max_mips="$mips"
    fi
    
    total_mips=$((total_mips + mips))
done

avg_mips=$(echo "scale=2; $total_mips / $num_iters" | bc -l)

echo "--------"
echo "Minimum MIPS: $min_mips"
echo "Maximum MIPS: $max_mips"
echo "Average MIPS: $avg_mips"
