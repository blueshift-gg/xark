//! Stamp the source revision into the `xark` CLI so `xark --version` identifies
//! the exact build (embedded via `env!`).
use std::path::Path;
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

/// The commit `cargo package` recorded, shortened like `git --short=12`.
fn packaged_sha() -> Option<String> {
    let manifest = Path::new(env!("CARGO_MANIFEST_DIR"));
    let text = std::fs::read_to_string(manifest.join(".cargo_vcs_info.json")).ok()?;
    // {"git": {"sha1": "<hex>"}, "path_in_vcs": "…"}
    let (_, after_key) = text.split_once("\"sha1\"")?;
    let (_, value) = after_key.split_once('"')?;
    let (sha, _) = value.split_once('"')?;
    if sha.len() < 12 || !sha.chars().all(|c| c.is_ascii_hexdigit()) {
        return None;
    }
    Some(sha[..12].to_string())
}

fn main() {
    let revision = packaged_sha()
        .or_else(|| git(&["rev-parse", "--short=12", "HEAD"]))
        .unwrap_or_else(|| "unknown".into());
    println!("cargo:rustc-env=XARK_GIT_HASH={revision}");
    println!("cargo:rerun-if-changed=build.rs");

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
