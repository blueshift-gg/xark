#!/usr/bin/env bash
# Build the xark-wasm package for the web (ESM, browser + Node).
# Usage: ./build.sh [web|nodejs|bundler] [dev|release]
set -euo pipefail

cd "$(dirname "$0")"

target="${1:-web}"
mode="${2:-release}"
out_dir="pkg"
[[ "$target" == "nodejs" ]] && out_dir="pkg-node"

if [[ "$mode" == "dev" ]]; then
  wasm-pack build --target "$target" --dev --out-dir "$out_dir" --scope blueshift-gg
else
  wasm-pack build --target "$target" --release --out-dir "$out_dir" --scope blueshift-gg
fi

echo "✅ built ($target, $mode) -> $out_dir/"
