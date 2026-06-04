#!/usr/bin/env bash
# Regenerate `Verifier.sol` for the smoke test by running
# `xark export evm` against the committed verifying-key fixture.
#
# Usage: ./tests/evm/regenerate.sh

set -euo pipefail

# Resolve workspace root from this script's directory.
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WORKSPACE="$(cd "${SCRIPT_DIR}/../.." && pwd)"

XARK_BIN="${WORKSPACE}/target/release/xark"
if [ ! -x "${XARK_BIN}" ]; then
    echo "Building xark in release mode..."
    (cd "${WORKSPACE}" && cargo build --release -p xark-cli)
fi

VK="${WORKSPACE}/tests/fixtures/groth16/arithmetic_square/verifying_key.bin"
OUT="${SCRIPT_DIR}/Verifier.sol"

"${XARK_BIN}" export evm \
    --verifying-key "${VK}" \
    --out "${OUT}"

echo "Wrote ${OUT}"
