#!/usr/bin/env bash
# The backend benchmark: the same function as a xark circuit proved by arkworks,
# by xark's own prover and by gnark, and written directly in gnark. Prints the
# table of benches/gnark/README.md for this machine.
#
#   benches/gnark/run.sh [runs]     # proofs per measurement (default 5), median taken
#
# Needs `go`. Every prover has its key in memory and all the cores; a time is
# the proof alone, without the witness solve xark does first (gnark's times
# include its own solver, which for a xark circuit only checks the rows).
set -euo pipefail

runs=${1:-5}
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
out=$root/target/bench-gnark
mkdir -p "$out"

cd "$root"
cargo build --release -q -p xark-cli
cargo build --release -q -p xark-groth16 --example bench_prove
(cd crates/cli/gnark && go build -o "$out/xark-gnark" .)
(cd "$here/pure" && go build -o "$out/pure-gnark" .)
xark=$root/target/release/xark
bench_prove=$root/target/release/examples/bench_prove
export XARK_GNARK=$out/xark-gnark

# The median of the numbers on stdin.
median() { sort -n | awk '{ v[NR] = $1 } END { print v[int((NR + 1) / 2)] }'; }
# `name=value` from a helper's report.
field() { sed -n "s/^$1=//p"; }

rows=()
bench() {
    local name=$1 crate=$2 inputs=$3 label=$4
    local keys=$out/$name
    rm -rf "$keys"
    # The template-reduced rows over a 2^k domain for every backend: the form
    # arkworks' prover takes, and so the same rows on each line of the table.
    # xark's key goes to a directory of its own; gnark's stays in the build's
    # `gnark/`, where `xark prove --backend gnark` reads it.
    "$xark" setup "$crate" --out "$keys" --r1cs-form reduced --domain radix2 >/dev/null 2>&1
    "$xark" setup "$crate" --r1cs-form reduced --backend gnark >/dev/null 2>&1
    local built
    built=$(dirname "$(find "$crate/target/xark" -name circuit.xbc | head -1)")
    local count
    count=$(sed -n 's/.*"num_constraints": *\([0-9]*\).*/\1/p' "$keys/metadata.json")

    local warm ark stream
    warm=$(for _ in $(seq $(((runs + 2) / 3))); do
        BENCH_TIME=1 "$bench_prove" warm "$built/circuit.xbc" "$keys/pk.bin" "$inputs"
    done)
    ark=$(echo "$warm" | awk '/warm prove/ { sub("s", "", $4); print $4 * 1000 }' | median)
    stream=$(echo "$warm" | awk '/warm prove/ { sub("s", "", $6); print $6 * 1000 }' | median)

    # The witness xark solves, as the file gnark proves from.
    "$xark" prove "$crate" --backend gnark --inputs "$inputs" >/dev/null 2>&1
    local g
    g=$("$XARK_GNARK" bench "$built/gnark" "$built/gnark/witness.wtns" "$runs")
    local p
    p=$("$out/pure-gnark" "$name" "$runs")

    rows+=("| $label | xark + arkworks | $count | $ark |")
    rows+=("| | xark + xark-groth16 | $count | $stream |")
    rows+=("| | xark + gnark | $(echo "$g" | field constraints) | $(echo "$g" | field prove_ms) |")
    rows+=("| | pure gnark | $(echo "$p" | field constraints) | $(echo "$p" | field prove_ms) |")
}

bench sha256 "$root/examples/sha256" "$here/sha256.inputs.json" "sha256 (3-byte message)"
bench poseidon2 "$root/examples/poseidon2" "$here/poseidon2.inputs.json" "poseidon2 (1 permutation)"
bench poseidon2_chain "$here/poseidon2_chain" "$here/poseidon2_chain/inputs.json" "poseidon2 (1000 permutations)"

echo "| function | frontend + backend | R1CS constraints | prove (ms) |"
echo "|---|---|---:|---:|"
printf '%s\n' "${rows[@]}"
