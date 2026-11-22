#!/usr/bin/env bash
# The backend benchmark: the same function as a xark circuit proved by arkworks,
# by xark's own prover and by gnark, and written directly in gnark. Prints the
# table of benches/gnark/README.md for this machine.
#
#   benches/gnark/run.sh [runs]     # proofs per measurement (default 5), median taken
#
# Needs `go`. Every prover has its key in memory; a time is the proof alone,
# without the witness solve xark does first (gnark's times include its own
# solver, which for a xark circuit only checks the rows). Each prover makes
# `runs` proofs in one process, twice over: with every core, and on one thread
# (`RAYON_NUM_THREADS=1` for the Rust provers; gnark's programs lower
# `GOMAXPROCS` to 1 themselves for a second round), which is the number about
# the work rather than the machine.
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
    "$xark" setup "$crate" --out "$keys" --r1cs-form reduced --domain radix2 >/dev/null 2>&1
    "$xark" setup "$crate" --out "$keys" --r1cs-form reduced --backend gnark >/dev/null 2>&1
    local built
    built=$(dirname "$(find "$crate/target/xark" -name circuit.xbc | head -1)")
    local count
    count=$(sed -n 's/.*"num_constraints": *\([0-9]*\).*/\1/p' "$keys/metadata.json")

    # arkworks and xark-groth16: `runs` proofs each, a line a proof.
    local warm warm1
    warm=$(BENCH_TIME=1 "$bench_prove" warm "$built/circuit.xbc" "$keys/pk.bin" "$inputs" "$runs")
    warm1=$(BENCH_TIME=1 RAYON_NUM_THREADS=1 "$bench_prove" warm "$built/circuit.xbc" "$keys/pk.bin" "$inputs" "$runs")
    ark() { awk '/warm prove/ { sub("s", "", $4); print $4 * 1000 }' | median; }
    stream() { awk '/warm prove/ { sub("s", "", $6); print $6 * 1000 }' | median; }

    # The witness xark solves, kept as the file gnark proves from.
    "$xark" prove "$crate" --backend gnark --proving-key "$keys/gnark/pk.bin" \
        --out "$keys" --keep-witness --inputs "$inputs" >/dev/null 2>&1
    local g p
    g=$("$XARK_GNARK" bench "$keys/gnark" "$keys/gnark/witness.wtns" "$runs")
    # The witness holds the inputs; the benchmark's are no secret, but nothing
    # is left behind that a real one would be.
    rm -f "$keys/gnark/witness.wtns"
    p=$("$out/pure-gnark" "$name" "$runs")

    rows+=("| $label | xark + arkworks | $count | $(echo "$warm" | ark) | $(echo "$warm1" | ark) |")
    rows+=("| | xark + xark-groth16 | $count | $(echo "$warm" | stream) | $(echo "$warm1" | stream) |")
    rows+=("| | xark + gnark | $(echo "$g" | field constraints) | $(echo "$g" | field prove_ms) | $(echo "$g" | field prove_1_ms) |")
    rows+=("| | pure gnark | $(echo "$p" | field constraints) | $(echo "$p" | field prove_ms) | $(echo "$p" | field prove_1_ms) |")
}

# A digest circuit's inputs are the message and digest `pure/` proves, written
# out by it under the xark circuit's names.
digest_inputs() {
    "$out/pure-gnark" inputs "$1" >"$out/$1.inputs.json"
    echo "$out/$1.inputs.json"
}

bench sha256 "$root/examples/sha256" "$(digest_inputs sha256)" "sha256 (3-byte message)"
bench keccak256 "$root/examples/keccak256" "$(digest_inputs keccak256)" "keccak256 (3-byte message)"
bench sha256_1024 "$here/sha256_1024" "$(digest_inputs sha256_1024)" "sha256 (1024-byte message)"
bench keccak256_1024 "$here/keccak256_1024" "$(digest_inputs keccak256_1024)" "keccak256 (1024-byte message)"
bench poseidon2 "$root/examples/poseidon2" "$here/poseidon2.inputs.json" "poseidon2 (1 permutation)"
bench poseidon2_chain "$here/poseidon2_chain" "$here/poseidon2_chain/inputs.json" "poseidon2 (1000 permutations)"

echo "| function | frontend + backend | R1CS constraints | prove (ms) | prove, 1 thread (ms) |"
echo "|---|---|---:|---:|---:|"
printf '%s\n' "${rows[@]}"
