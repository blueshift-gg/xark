//! Stamp the git revision into the `xark` CLI so `xark --version` identifies the
//! exact build (embedded via `env!`).
use std::process::Command;

fn git(args: &[&str]) -> Option<String> {
    Command::new("git")
        .args(args)
        .output()
        .ok()
        .filter(|out| out.status.success())
        .map(|out| String::from_utf8_lossy(&out.stdout).trim().to_string())
        .filter(|value| !value.is_empty())
}

fn main() {
    let git_hash = git(&["rev-parse", "--short=12", "HEAD"]).unwrap_or_else(|| "unknown".into());
    println!("cargo:rustc-env=XARK_GIT_HASH={git_hash}");
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

    // Watching HEAD suffices when detached; on a branch, also watch the
    // referenced file because HEAD itself does not change.
    if let Some(head) = git(&["rev-parse", "--git-path", "HEAD"]) {
        println!("cargo:rerun-if-changed={head}");
    }
    if let Some(reference) = git(&["symbolic-ref", "-q", "HEAD"])
        && let Some(path) = git(&["rev-parse", "--git-path", &reference])
    {
        println!("cargo:rerun-if-changed={path}");
    }
}
