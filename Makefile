WASM_DIR := crates/wasm
WASM_PKG := $(WASM_DIR)/pkg
WASM_NODE := $(WASM_DIR)/pkg-node

.PHONY: wasm wasm-dev smoke clean

# Build the release wasm package (target: web — ESM, browser + Node).
wasm:
	cd $(WASM_DIR) && wasm-pack build --target web --release

# Node.js dev build (fast compile, useful for the smoke test).
wasm-dev:
	cd $(WASM_DIR) && wasm-pack build --target nodejs --dev --out-dir pkg-node

# Run the xark-wasm smoke tests (builds wasm-dev first if needed).
smoke: wasm-dev
	cd $(WASM_DIR) && node --test tests/wasm-smoke.test.cjs

# Remove wasm-pack output dirs.
clean:
	rm -rf $(WASM_PKG) $(WASM_NODE)
