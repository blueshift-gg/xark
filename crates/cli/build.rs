//! Stamp the source identity into the `xark` CLI so `xark --version` identifies
//! the exact build, plus the CLI-only extras: the source root (for dirty-build
//! path pinning) and the driver's pinned nightly. The identity computation is
//! shared with `xark-rustc`'s build script via `xark-build-identity` — the
//! doctor parity check requires the two to agree byte-for-byte.

fn main() {
    let identity = xark_build_identity::emit();
    println!(
        "cargo:rustc-env=XARK_SOURCE_ROOT={}",
        identity.source_root.as_deref().unwrap_or("")
    );
    println!("cargo:rerun-if-changed=build.rs");

    // Single source of truth for the nightly the `xark-rustc` driver needs: the
    // driver crate's `rust-toolchain.toml`. Embedding it keeps `xark init` hints
    // and reinstall messages tied to the exact driver the CLI ships with, so the
    // two never drift.
    let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap_or_default();
    let toolchain = std::path::Path::new(&manifest).join("../rustc/rust-toolchain.toml");
    println!("cargo:rerun-if-changed={}", toolchain.display());
    let nightly = std::fs::read_to_string(&toolchain)
        .ok()
        .and_then(|s| {
            s.lines()
                .find_map(|l| l.trim().strip_prefix("channel ="))
                .map(|v| v.trim().trim_matches('"').to_string())
        })
        // Fallback for a standalone (crates.io) build where the driver crate is
        // not a sibling. Keep in sync with `crates/rustc/rust-toolchain.toml`.
        .unwrap_or_else(|| "nightly-2026-05-03".to_string());
    println!("cargo:rustc-env=XARK_NIGHTLY={nightly}");
}
