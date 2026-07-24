#!/usr/bin/env bash
# Build the xark-wasm package. All standard wasm-pack targets are available,
# plus a `module` target for Cloudflare Workers (workerd):
#
#   nodejs   -> dist/node/     wasm-pack --target nodejs   (Node.js)
#   web      -> dist/web/      wasm-pack --target web      (browser / manual init)
#   bundler  -> dist/bundler/  wasm-pack --target bundler  (webpack, rollup, …)
#   module   -> dist/module/   wasm-bindgen --target module (Cloudflare Workers)
#
# Every target except `module` is a plain wasm-pack build, so xark-wasm is a
# normal, generally-applicable wasm-pack package. The `module` target exists
# because Cloudflare workerd hands `import "./x.wasm"` back as a
# `WebAssembly.Module` (not callable exports), and `--target module` is the one
# wasm-bindgen output that instantiates that Module inline — the same approach
# Cloudflare's own `worker-build` uses. wasm-pack doesn't expose
# `--target module`, so we invoke wasm-bindgen directly for that one target.
#
# Usage: ./build.sh [nodejs|web|bundler|module] [dev|release]
set -euo pipefail

cd "$(dirname "$0")"

target="${1:-bundler}"
mode="${2:-release}"

case "$target" in
  nodejs)  out_dir="dist/node" ;;
  web)     out_dir="dist/web" ;;
  bundler) out_dir="dist/bundler" ;;
  module)  out_dir="dist/module" ;;
  *)       echo "unknown target: $target (want nodejs|web|bundler|module)"; exit 1 ;;
esac

if [[ "$target" != "module" ]]; then
  dev_flag=""
  [[ "$mode" == "dev" ]] && dev_flag="--dev"
  wasm-pack build --target "$target" ${dev_flag:---release} --out-dir "$out_dir" --no-pack
  rm -f "$out_dir/.gitignore"
  echo "✅ built ($target, $mode) -> $out_dir/"
  exit 0
fi

# ---- module target: wasm-bindgen directly (wasm-pack can't do --target module)

# Pin the CLI to the exact `wasm-bindgen` crate version so the generated JS glue
# matches the wasm's embedded schema. A drift here fails only at runtime.
want="$(cargo metadata --format-version 1 --locked 2>/dev/null \
  | grep -o '"name":"wasm-bindgen","version":"[^"]*"' | head -1 \
  | grep -o '[0-9][0-9.]*')"
have="$(wasm-bindgen --version 2>/dev/null | grep -o '[0-9][0-9.]*' || true)"
if [[ -z "$have" ]]; then
  echo "error: wasm-bindgen CLI not found. Install the pinned version:"
  echo "  cargo install wasm-bindgen-cli --version $want --locked"
  exit 1
fi

if [[ -n "$want" && "$have" != "$want" ]]; then
  echo "error: wasm-bindgen CLI $have != crate $want (schema mismatch). Run:"
  echo "  cargo install wasm-bindgen-cli --version $want --locked"
  exit 1
fi

profile="debug"; [[ "$mode" == "release" ]] && profile="release"
cargo_flag=""; [[ "$profile" == "release" ]] && cargo_flag="--release"

cargo build $cargo_flag --target wasm32-unknown-unknown
wasm-bindgen "target/wasm32-unknown-unknown/$profile/xark_wasm.wasm" \
  --out-dir "$out_dir" \
  --target module \
  --out-name xark_wasm

# wasm-bindgen's `--target module` emits `import source X from "./x.wasm"`. The
# `source` keyword isn't understood by some bundlers/engines (e.g. esbuild), and
# a plain `import X` is what hands back the `WebAssembly.Module` workerd expects.
# A no-op if a future wasm-bindgen drops the keyword.
sed -i 's|^import source |import |' "$out_dir/xark_wasm.js"

if [[ "$mode" == "release" ]]; then
  wasm-pack build --target bundler --release --out-dir dist/bundler --no-pack
  rm -f dist/bundler/.gitignore
  cp dist/bundler/xark_wasm_bg.wasm "$out_dir/xark_wasm_bg.wasm"
  echo "   reused wasm-pack's optimized wasm (dist/bundler/xark_wasm_bg.wasm)"
fi

echo "✅ built (module, $mode) -> $out_dir/"
