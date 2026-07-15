#!/usr/bin/env bash
# Build the xark-wasm package. All standard wasm-pack targets are available,
# plus a `module` target for Cloudflare Workers (workerd):
#
#   nodejs   -> pkg-node/     wasm-pack --target nodejs   (Node.js)
#   web      -> pkg-web/      wasm-pack --target web      (browser / manual init)
#   bundler  -> pkg-bundler/  wasm-pack --target bundler  (webpack, rollup, …)
#   module   -> pkg-module/   wasm-bindgen --target module (Cloudflare Workers)
#
# Every target except `module` is a plain wasm-pack build, so xark-wasm is a
# normal, generally-applicable wasm-pack package. The `module` target exists
# only because workerd hands `import "./x.wasm"` back as a `WebAssembly.Module`
# (not callable exports), and `--target module` is the one wasm-bindgen output
# that instantiates that Module inline — the same approach Cloudflare's own
# `worker-build` uses. wasm-pack doesn't expose `--target module`, so we invoke
# wasm-bindgen directly for that one target (its version is pinned to the
# `wasm-bindgen` crate to avoid the schema-mismatch panic).
#
# Usage: ./build.sh [nodejs|web|bundler|module] [dev|release]
set -euo pipefail

cd "$(dirname "$0")"

target="${1:-module}"
mode="${2:-release}"

case "$target" in
  nodejs)  out_dir="pkg-node" ;;
  web)     out_dir="pkg-web" ;;
  bundler) out_dir="pkg-bundler" ;;
  module)  out_dir="pkg-module" ;;
  *)       echo "unknown target: $target (want nodejs|web|bundler|module)"; exit 1 ;;
esac

if [[ "$target" != "module" ]]; then
  dev_flag=""
  [[ "$mode" == "dev" ]] && dev_flag="--dev"
  wasm-pack build --target "$target" ${dev_flag:---release} --out-dir "$out_dir" --scope blueshift-gg
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

# wasm-bindgen's `--target module` emits `import source X from "./x.wasm"`; the
# `source` phase-import keyword isn't understood by esbuild/Wrangler yet, and a
# plain `import X` gives the `WebAssembly.Module` we want. Same fix worker-build
# applies. (Harmless if a future wasm-bindgen drops the keyword.)
sed -i 's|^import source |import |' "$out_dir/xark_wasm.js"
# Optimize the wasm by reusing what wasm-pack already produced. wasm-pack runs
# wasm-opt automatically on its targets, and the *raw* wasm-bindgen wasm is
# byte-identical across targets (only the JS glue differs), so wasm-pack's
# optimized `bundler` wasm is exactly what this module JS expects. No separate
# wasm-opt install / PATH hunt / cache-path guessing; the optimization is done
# the same way, and platform-portably, as every other target. (Release only;
# dev skips optimization.)
#
# We always rebuild `bundler` here rather than reusing a pre-existing
# `pkg-bundler/xark_wasm_bg.wasm`: a stale copy (from an earlier source build)
# would be optimized wasm that no longer matches the JS glue wasm-bindgen just
# generated, and the embedded schema hashes would disagree at runtime.
if [[ "$mode" == "release" ]]; then
  wasm-pack build --target bundler --release --out-dir pkg-bundler --scope blueshift-gg
  cp pkg-bundler/xark_wasm_bg.wasm "$out_dir/xark_wasm_bg.wasm"
  echo "   reused wasm-pack's optimized wasm (pkg-bundler/xark_wasm_bg.wasm)"
fi

echo "✅ built (module, $mode) -> $out_dir/"
