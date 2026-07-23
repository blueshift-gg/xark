//! Source-identity stamping shared by the `xark-cli` and `xark-rustc` build
//! scripts.
//!
//! `xark doctor` enforces CLI/driver parity by comparing the identity strings
//! both binaries baked in at build time, and `xark init`/`xark export` pin
//! generated manifests to them. That only works if the two build scripts agree
//! byte-for-byte on what "this exact source" means — so the computation lives
//! here, once, and each build script calls [`emit`].
//!
//! Identity is scoped to the paths that determine compiler/CLI behavior
//! (`Cargo.toml`, `Cargo.lock`, `crates/`, `gadgets/`): a clean checkout is its
//! revision; a dirty one appends a content fingerprint of the scoped changes so
//! two different edits of the same base commit can never pass the parity check
//! against each other.

use std::io::Write;
use std::process::{Command, Stdio};

/// The pathspecs whose content defines the source identity. `:(top)` makes them
/// repo-root-relative, so the same commands work from either crate directory.
const IDENTITY_PATHS: [&str; 4] = [
    ":(top)Cargo.toml",
    ":(top)Cargo.lock",
    ":(top)crates",
    ":(top)gadgets",
];

/// The source identity stamped into a binary at build time.
pub struct SourceIdentity {
    /// Full revision; `+<fingerprint>-dirty` when the scoped worktree has
    /// uncommitted changes; `"unknown"` outside a git checkout.
    pub git_hash: String,
    /// Short (12-char revision) form of the same, with the same dirty suffix.
    pub git_hash_short: String,
    /// Absolute path of the git worktree root, when available.
    pub source_root: Option<String>,
}

/// Compute the identity and print the cargo directives that stamp and keep it
/// fresh: the `XARK_GIT_HASH` / `XARK_GIT_HASH_SHORT` env vars, a
/// `rerun-if-changed` per identity source file, and watches on git's `HEAD`
/// (plus the branch ref it points at) so commits re-stamp too.
///
/// Watching every tracked+untracked file under the identity paths means any
/// source edit anywhere in `crates/`/`gadgets/` reruns both build scripts on
/// the next build. That is deliberate: the dirty fingerprint is a content hash,
/// so nothing short of re-reading the files can keep it exact, and a stale
/// fingerprint would defeat the parity check the identity exists for. The rerun
/// itself is a handful of git subprocesses; dependent crates only recompile
/// when the emitted values actually change.
pub fn emit() -> SourceIdentity {
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
    watch_identity_files();

    // Resolve paths through git so this works from the nested crate and from a
    // linked worktree. Watching HEAD is sufficient when detached; on a branch,
    // also watch the referenced file because HEAD itself does not change.
    if let Some(head) = git(&["rev-parse", "--git-path", "HEAD"]) {
        println!("cargo:rerun-if-changed={head}");
    }
    if let Some(reference) = git(&["symbolic-ref", "-q", "HEAD"])
        && let Some(path) = git(&["rev-parse", "--git-path", &reference])
    {
        println!("cargo:rerun-if-changed={path}");
    }

    SourceIdentity {
        git_hash,
        git_hash_short,
        source_root,
    }
}

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
    let mut args = vec!["status", "--porcelain", "--"];
    args.extend(IDENTITY_PATHS);
    Command::new("git")
        .args(args)
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
    let mut args = vec!["diff", "--binary", "HEAD", "--"];
    args.extend(IDENTITY_PATHS);
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
    untracked_args.extend(IDENTITY_PATHS);
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
    let mut args = vec![
        "ls-files",
        "--full-name",
        "--cached",
        "--others",
        "--exclude-standard",
        "--",
    ];
    args.extend(IDENTITY_PATHS);
    let Some(files) = git(&args) else {
        return;
    };
    for file in files.lines() {
        println!("cargo:rerun-if-changed={root}/{file}");
    }
}
