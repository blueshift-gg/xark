//! Stamp the git revision into the `xark` CLI so `xark --version` identifies the
//! exact build (embedded via `env!`).
use std::io::Write;
use std::process::{Command, Stdio};

fn git(args: &[&str]) -> Option<String> {
    Command::new("git")
        .args(args)
        .output()
        .ok()
        .filter(|out| out.status.success())
        .map(|out| String::from_utf8_lossy(&out.stdout).trim().to_string())
        .filter(|value| !value.is_empty())
}

fn git_dirty() -> bool {
    Command::new("git")
        .args([
            "status",
            "--porcelain",
            "--",
            ":(top)Cargo.toml",
            ":(top)Cargo.lock",
            ":(top)crates",
            ":(top)gadgets",
        ])
        .output()
        .ok()
        .filter(|out| out.status.success())
        .is_some_and(|out| !out.stdout.is_empty())
}

/// Content-address the scoped dirty worktree so two binaries built from
/// different edits to the same base commit cannot falsely pass the CLI/driver
/// parity check. Tracked changes come from one binary diff; untracked source
/// files are appended with their path and bytes before Git hashes the stream.
fn dirty_fingerprint() -> Option<String> {
    const PATHS: [&str; 4] = [
        ":(top)Cargo.toml",
        ":(top)Cargo.lock",
        ":(top)crates",
        ":(top)gadgets",
    ];
    let mut args = vec!["diff", "--binary", "HEAD", "--"];
    args.extend(PATHS);
    let mut material = Command::new("git")
        .args(args)
        .output()
        .ok()
        .filter(|out| out.status.success())?
        .stdout;

    let mut untracked_args = vec![
        "ls-files",
        "--full-name",
        "--others",
        "--exclude-standard",
        "--",
    ];
    untracked_args.extend(PATHS);
    let untracked = git(&untracked_args).unwrap_or_default();
    let root = git(&["rev-parse", "--show-toplevel"])?;
    for path in untracked.lines() {
        material.extend_from_slice(b"\0untracked\0");
        material.extend_from_slice(path.as_bytes());
        material.push(0);
        material.extend_from_slice(&std::fs::read(std::path::Path::new(&root).join(path)).ok()?);
    }

    let mut child = Command::new("git")
        .args(["hash-object", "--stdin"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .ok()?;
    child.stdin.take()?.write_all(&material).ok()?;
    let output = child.wait_with_output().ok()?;
    output
        .status
        .success()
        .then(|| String::from_utf8_lossy(&output.stdout).trim().to_string())
}

fn watch_identity_files() {
    let Some(root) = git(&["rev-parse", "--show-toplevel"]) else {
        return;
    };
    let Some(files) = git(&[
        "ls-files",
        "--full-name",
        "--cached",
        "--others",
        "--exclude-standard",
        "--",
        ":(top)Cargo.toml",
        ":(top)Cargo.lock",
        ":(top)crates",
        ":(top)gadgets",
    ]) else {
        return;
    };
    for file in files.lines() {
        println!("cargo:rerun-if-changed={root}/{file}");
    }
}

fn main() {
    let source_root = git(&["rev-parse", "--show-toplevel"]);
    let mut git_hash = git(&["rev-parse", "HEAD"]).unwrap_or_else(|| "unknown".into());
    let mut git_hash_short =
        git(&["rev-parse", "--short=12", "HEAD"]).unwrap_or_else(|| "unknown".into());
    if git_hash != "unknown" && git_dirty() {
        let fingerprint = dirty_fingerprint().unwrap_or_else(|| "unknown".into());
        git_hash.push_str(&format!("+{fingerprint}-dirty"));
        git_hash_short.push_str(&format!(
            "+{}-dirty",
            fingerprint.get(..12).unwrap_or(&fingerprint)
        ));
    }
    println!("cargo:rustc-env=XARK_GIT_HASH={git_hash}");
    println!("cargo:rustc-env=XARK_GIT_HASH_SHORT={git_hash_short}");
    println!(
        "cargo:rustc-env=XARK_SOURCE_ROOT={}",
        source_root.as_deref().unwrap_or("")
    );
    println!("cargo:rerun-if-changed=build.rs");
    watch_identity_files();

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
