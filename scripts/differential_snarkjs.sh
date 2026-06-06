#!/usr/bin/env bash
# Differential test: prove each circuit with xark (arkworks Groth16), then
# verify the proof with snarkjs — a fully independent implementation. If
# snarkjs accepts our proof, our proof encoding + the Groth16 verification
# equation are validated against a separate stack. Also runs a negative
# control (tampered public input must be rejected).
#
# Usage: scripts/differential_snarkjs.sh [circuit ...]   (default: all but ecdsa)
set -euo pipefail
cd "$(dirname "$0")/.."

XARK=target/release/xark
[ -x "$XARK" ] || cargo build --release -p xark-cli >/dev/null
cargo build -q -p xark-tests --example to_snarkjs

FX=crates/tests/fixtures
WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT

if [ "$#" -gt 0 ]; then circuits="$*"; else
  # ecdsa_* excluded by default: multi-hundred-MB setup. Pass them explicitly.
  circuits=$(ls "$FX"/*.json | xargs -n1 basename | sed 's/.json$//' \
             | grep -vE '^(unsupported_|ecdsa_)')
fi

pass=0; fail=0
for c in $circuits; do
  d="$WORK/$c"; mkdir -p "$d"
  $XARK setup --artifact "$FX/$c.json" --out "$d" --insecure-dev-mode --deterministic-rng 1 >/dev/null 2>&1
  $XARK prove --artifact "$FX/$c.json" --witness "$FX/$c.gz" \
        --proving-key "$d/proving_key.bin" --out "$d/proof.bin" --deterministic-rng 1 >/dev/null 2>&1
  cargo run -q -p xark-tests --example to_snarkjs -- "$d" "$d" >/dev/null 2>&1

  if snarkjs groth16 verify "$d/vkey.json" "$d/public.json" "$d/proof.json" >/dev/null 2>&1; then
    # Negative control: tampering any public input must make snarkjs reject.
    n=$(jq 'length' "$d/public.json")
    neg_ok=1
    if [ "$n" -gt 0 ]; then
      jq '.[0]=((.[0]|tonumber+1)|tostring)' "$d/public.json" > "$d/public_bad.json"
      if snarkjs groth16 verify "$d/vkey.json" "$d/public_bad.json" "$d/proof.json" >/dev/null 2>&1; then
        neg_ok=0  # tampered proof wrongly accepted
      fi
    fi
    if [ "$neg_ok" -eq 1 ]; then printf '%-26s snarkjs OK (N=%s)\n' "$c" "$n"; pass=$((pass+1));
    else printf '%-26s NEGATIVE-CONTROL FAILED\n' "$c"; fail=$((fail+1)); fi
  else
    printf '%-26s snarkjs REJECTED our proof\n' "$c"; fail=$((fail+1))
  fi
done
echo "----"; echo "snarkjs differential: $pass passed, $fail failed"
[ "$fail" -eq 0 ]
