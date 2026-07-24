#!/usr/bin/env bash
# Build xark-wasm for JS targets. Usage: ./build.sh [nodejs|web|bundler|module|all] [dev|release]
# `module` uses wasm-bindgen --target module (workerd needs a self-instantiating
# WebAssembly.Module that wasm-pack can't emit); `all` = nodejs + web + module.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")"

build() {
  local target="$1" mode="$2" out_dir
  case "$target" in
    nodejs)  out_dir="dist/node" ;;
    web)     out_dir="dist/web" ;;
    bundler) out_dir="dist/bundler" ;;
    module)  out_dir="dist/module" ;;
    *) echo "unknown target: $target (want nodejs|web|bundler|module|all)" >&2; return 1 ;;
  esac

  if [[ "$target" != "module" ]]; then
    local dev_flag=""
    [[ "$mode" == "dev" ]] && dev_flag="--dev"
    wasm-pack build --target "$target" ${dev_flag:---release} --out-dir "$out_dir" --no-pack
    rm -f "$out_dir/.gitignore"
    echo "✅ built ($target, $mode) -> $out_dir/"
    return
  fi

  # The wasm-bindgen CLI must match the library baked into the .wasm exactly, or
  # the emitted JS glue won't match the wasm's schema (fails only at runtime).
  local want
  want="$(awk '/^name = "wasm-bindgen"$/{f=1;next} f&&/^version = /{sub(/^version = "/,"");sub(/"$/,"");print;exit}' ../../Cargo.lock)"
  [[ -n "$want" ]] || { echo "error: could not resolve wasm-bindgen version from Cargo.lock." >&2; return 1; }

  local have
  have="$(wasm-bindgen --version 2>/dev/null | grep -o '[0-9][0-9.]*' | head -1 || true)"
  if [[ -z "$have" ]]; then
    echo "wasm-bindgen-cli not found; installing $want …"
    cargo install wasm-bindgen-cli --version "$want" --locked
  elif [[ "$have" != "$want" ]]; then
    echo "error: wasm-bindgen CLI $have != required $want. Re-pin:" >&2
    echo "  cargo install wasm-bindgen-cli --version $want --locked --force" >&2
    return 1
  fi

  local profile="debug"; [[ "$mode" == "release" ]] && profile="release"
  local cargo_flag=""; [[ "$profile" == "release" ]] && cargo_flag="--release"

  cargo build $cargo_flag --target wasm32-unknown-unknown
  wasm-bindgen "target/wasm32-unknown-unknown/$profile/xark_wasm.wasm" \
    --out-dir "$out_dir" --target module --out-name xark_wasm

  # workerd/esbuild reject the `import source` keyword; rewrite to a plain import.
  sed -i 's|^import source |import |' "$out_dir/xark_wasm.js"

  if [[ "$mode" == "release" ]]; then
    wasm-pack build --target bundler --release --out-dir dist/bundler --no-pack
    rm -f dist/bundler/.gitignore
    cp dist/bundler/xark_wasm_bg.wasm "$out_dir/xark_wasm_bg.wasm"
  fi

  echo "✅ built (module, $mode) -> $out_dir/"
}

target="${1:-bundler}"
mode="${2:-release}"

if [[ "$target" == "all" ]]; then
  build nodejs "$mode"
  build web "$mode"
  build module "$mode"
  echo "✅ built (all, $mode) -> dist/{node,web,module,bundler}/"
else
  build "$target" "$mode"
fi
