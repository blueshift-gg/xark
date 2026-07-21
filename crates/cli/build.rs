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

    // Watching HEAD suffices when detached; on a branch, also watch the
    // referenced file because HEAD itself does not change.
    if let Some(head) = git(&["rev-parse", "--git-path", "HEAD"]) {
        println!("cargo:rerun-if-changed={head}");
    }
    if let Some(reference) = git(&["symbolic-ref", "-q", "HEAD"]) {
        if let Some(path) = git(&["rev-parse", "--git-path", &reference]) {
            println!("cargo:rerun-if-changed={path}");
        }
    }
}
