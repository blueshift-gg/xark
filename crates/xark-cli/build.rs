//! Stamp the git revision into the `xark` CLI so `xark --version` (and the
//! exported verifier crate's reproducible-build metadata) identify the exact
//! build. The nightly sysroot/toolchain capture lives in `xark-rustc`'s
//! `build.rs`; the CLI only needs the git hash it embeds via `env!`.
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
    // Stamp the git revision so `xark --version` identifies the exact build
    // (a stale `~/.cargo/bin/xark` vs a fresh `--path` install are otherwise
    // indistinguishable — both just say the crate version).
    let git_hash = git(&["rev-parse", "--short=12", "HEAD"]).unwrap_or_else(|| "unknown".into());
    println!("cargo:rustc-env=XARK_GIT_HASH={git_hash}");
    println!("cargo:rerun-if-changed=build.rs");

    // Resolve paths through git so this works from the nested crate and from a
    // linked worktree. Watching HEAD is sufficient when detached; on a branch,
    // also watch the referenced file because HEAD itself does not change.
    if let Some(head) = git(&["rev-parse", "--git-path", "HEAD"]) {
        println!("cargo:rerun-if-changed={head}");
    }
    if let Some(reference) = git(&["symbolic-ref", "-q", "HEAD"]) {
        if let Some(path) = git(&["rev-parse", "--git-path", &reference]) {
            println!("cargo:rerun-if-changed={path}");
        }
    }
}
