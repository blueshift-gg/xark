#!/usr/bin/env bash
# Regenerate committed Solana test vectors from a REAL trusted-setup ceremony
# (snarkjs phase-1 powers-of-tau -> xark phase-2), instead of insecure-dev-mode.
#
# Usage:
#   scripts/ceremony_vectors.sh <power> [circuit ...]
#
# <power> is the phase-1 size (2^power must cover the largest circuit's
# constraint count): e.g. 12 for the small circuits, 18 for keccak. With no
# circuits listed, regenerates every circuit whose constraint count fits 2^power.
#
# The phase-1 contribution entropy and the phase-2 seed below are FIXED so the
# vectors are reproducible. For a real production ceremony, replace them with
# genuine independent contributions and a public beacon, and record the
# transcript (see docs/trusted-setup.md).
set -euo pipefail
cd "$(dirname "$0")/.."

POWER="${1:?usage: ceremony_vectors.sh <power> [circuit ...]}"; shift || true
PHASE2_SEED=00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff
ENTROPY="xark-test-vector-ceremony-fixed-entropy-do-not-use-in-prod"
BEACON=0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20

XARK=target/release/xark
[ -x "$XARK" ] || cargo build --release -p xark-cli >/dev/null
cargo build -q -p xark-tests --example to_snarkjs

W=$(mktemp -d); trap 'rm -rf "$W"' EXIT
FX=crates/tests/fixtures

echo "== phase 1: powers of tau (2^$POWER) =="
snarkjs powersoftau new bn128 "$POWER" "$W/p0.ptau" >/dev/null
snarkjs powersoftau contribute "$W/p0.ptau" "$W/p1.ptau" --name=c1 -e="$ENTROPY" >/dev/null
snarkjs powersoftau beacon "$W/p1.ptau" "$W/pb.ptau" "$BEACON" 10 -n=beacon >/dev/null
snarkjs powersoftau prepare phase2 "$W/pb.ptau" "$W/final.ptau" >/dev/null

if [ "$#" -gt 0 ]; then circuits="$*"; else
  circuits=$(ls "$FX"/*.json | xargs -n1 basename | sed 's/.json$//' | grep -vE '^unsupported_')
fi

for c in $circuits; do
  d="$W/$c"; mkdir -p "$d"
  if ! $XARK setup --artifact "$FX/$c.json" --out "$d" \
       --ptau-file "$W/final.ptau" --phase2-seed "$PHASE2_SEED" >/dev/null 2>"$d/err"; then
    printf '%-26s SKIP (%s)\n' "$c" "$(tail -1 "$d/err" | head -c 60)"; continue
  fi
  $XARK prove --artifact "$FX/$c.json" --witness "$FX/$c.gz" \
        --proving-key "$d/proving_key.bin" --out "$d/proof.bin" >/dev/null 2>&1
  $XARK export --verifying-key "$d/verifying_key.bin" --proof "$d/proof.bin" \
        --public-inputs "$d/public_inputs.json" --out "$d" >/dev/null 2>&1
  # Independent sanity: snarkjs must accept the ceremony-keyed proof.
  cargo run -q -p xark-tests --example to_snarkjs -- "$d" "$d" >/dev/null 2>&1
  snarkjs groth16 verify "$d/vkey.json" "$d/public.json" "$d/proof.json" >/dev/null 2>&1 \
    || { printf '%-26s snarkjs REJECTED ceremony proof!\n' "$c"; continue; }
  # Install the ceremony vectors over the committed ones.
  out="$FX/groth16/$c"; mkdir -p "$out"
  cp "$d"/{verifying_key.solana.bin,proof.solana.bin,public_inputs.solana.bin,instruction_data.bin} "$out/"
  printf '%-26s regenerated from ceremony (snarkjs OK)\n' "$c"
done
echo "Done. Re-run the verifier test suites and update any committed hash pins."
