#!/usr/bin/env bash
# Many witnesses per circuit (addresses the "one KAT per gadget" gap).
#
# For circuits whose public output is a simple function of the input, generate
# a diverse set of inputs (edge cases + spread) via nargo (the ground-truth
# ACVM solver), then run the full xark pipeline on each. `xark prove` now
# self-verifies, so a successful prove means: the witness satisfied our lowered
# R1CS (completeness) AND the resulting proof verifies. Any input where nargo
# solves a witness but xark fails to prove/verify is a lowering bug.
#
# Extending to the hash gadgets (sha256/keccak/blake/poseidon) requires
# computing their expected public outputs to build Prover.toml — mechanical but
# per-gadget; left as follow-up. This harness covers the circuits with
# trivially-variable inputs and demonstrates the methodology.
set -euo pipefail
cd "$(dirname "$0")/.."
XARK="$(pwd)/target/release/xark"
[ -x "$XARK" ] || cargo build --release -p xark-cli >/dev/null

run_circuit() {  # $1=circuit  $2=newline-separated "proverToml|||label" cases
  local c="$1" cases="$2"
  local dir="crates/tests/circuits/$c" work
  work=$(mktemp -d)
  ( cd "$dir" && nargo compile >/dev/null 2>&1 )
  local acir="$dir/target/$c.json"
  "$XARK" setup --artifact "$acir" --out "$work" --insecure-dev-mode --deterministic-rng 1 >/dev/null 2>&1
  local pass=0 fail=0
  while IFS= read -r line; do
    [ -z "$line" ] && continue
    local toml="${line%%|||*}" label="${line##*|||}"
    printf '%b' "$toml" > "$dir/Prover.toml"
    if ! ( cd "$dir" && nargo execute w >/dev/null 2>&1 ); then
      printf '  %-22s nargo could not solve (skipped)\n' "$label"; continue
    fi
    if "$XARK" prove --artifact "$acir" --witness "$dir/target/w.gz" \
        --proving-key "$work/proving_key.bin" --out "$work/proof.bin" \
        --deterministic-rng 1 >/dev/null 2>&1 \
       && "$XARK" verify --verifying-key "$work/verifying_key.bin" --proof "$work/proof.bin" \
        --public-inputs "$work/public_inputs.json" 2>&1 | grep -q 'verified: true'; then
      pass=$((pass+1))
    else
      printf '  %-22s PROVE/VERIFY FAILED (nargo solved it!)\n' "$label"; fail=$((fail+1))
    fi
  done <<< "$cases"
  rm -rf "$work"
  printf '%-20s %d witnesses verified, %d failed\n' "$c" "$pass" "$fail"
  [ "$fail" -eq 0 ]
}

# arithmetic_square: main(x: Field, y: pub Field) asserts x*x == y.
as_cases=""
for x in 0 1 2 3 7 42 255 256 65535 65536 4294967296 9223372036854775808 12345678901234567890; do
  y=$(python3 -c "print($x*$x)")
  as_cases+="x = \"$x\"\ny = \"$y\"\n|||x=$x"$'\n'
done

# range_basic: main(x: u8, out: pub Field) — out == x, x range-checked < 256.
rb_cases=""
for x in 0 1 2 127 128 200 254 255; do
  rb_cases+="x = \"$x\"\nout = \"$x\"\n|||x=$x"$'\n'
done

ok=0
run_circuit arithmetic_square "$as_cases" || ok=1
run_circuit range_basic "$rb_cases" || ok=1
# restore committed Prover.tomls
printf 'x = "9"\ny = "81"\n' > crates/tests/circuits/arithmetic_square/Prover.toml
printf 'x = "200"\nout = "200"\n' > crates/tests/circuits/range_basic/Prover.toml
exit $ok
