//! Capture the toolchain the `xark` binary is built with, so the CLI can drive
//! `cargo`/the rustc-driver with the *same* nightly (sysroot + toolchain),
//! independent of the ambient toolchain where `xark build` is later run.
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

/// Content-address the scoped dirty worktree so the compiler driver identity is
/// exact even before the source changes have been committed.
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
    output.status.success().then(|| {
        String::from_utf8_lossy(&output.stdout)
            .trim()
            .to_string()
    })
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
    let rustc = std::env::var("RUSTC").unwrap_or_else(|_| "rustc".into());
    if let Ok(out) = Command::new(&rustc).args(["--print", "sysroot"]).output()
        && out.status.success()
    {
        let sysroot = String::from_utf8_lossy(&out.stdout).trim().to_string();
        let tc = std::path::Path::new(&sysroot)
            .file_name()
            .and_then(|s| s.to_str())
            .unwrap_or("nightly")
            .to_string();
        println!("cargo:rustc-env=XARK_SYSROOT={sysroot}");
        println!("cargo:rustc-env=XARK_TOOLCHAIN={tc}");
        // Bake the toolchain lib dir into the binary rpath so librustc_driver
        // loads at runtime without DYLD_LIBRARY_PATH / LD_LIBRARY_PATH.
        println!("cargo:rustc-link-arg-bins=-Wl,-rpath,{sysroot}/lib");

        // Guardrail: if built against the FLOATING `nightly` channel (dir name
        // `nightly-<target>`, no date) rather than the pinned `nightly-YYYY-MM-DD`,
        // the baked rpath points at a rolling dir that `rustup update` will move
        // out from under the binary — causing a `dyld: librustc_driver … not
        // loaded` failure later. Warn loudly and say how to fix it.
        let floating = tc
            .strip_prefix("nightly-")
            .is_some_and(|rest| !rest.starts_with(|c: char| c.is_ascii_digit()));
        if floating {
            println!(
                "cargo:warning=xark built against the FLOATING `nightly` toolchain \
                     ({tc}); its librustc_driver rpath will break on `rustup update`. \
                     Install with the pinned toolchain instead: \
                     `cargo +nightly-2026-05-03 install --path crates/lang --features cli` \
                     (or run the install from within `crates/lang/`)."
            );
        }
    }
    // Stamp the git revision so `xark --version` identifies the exact build
    // (a stale `~/.cargo/bin/xark` vs a fresh `--path` install are otherwise
    // indistinguishable — both just say the crate version).
    let mut git_hash = git(&["rev-parse", "HEAD"]).unwrap_or_else(|| "unknown".into());
    let mut git_hash_short = git(&["rev-parse", "--short=12", "HEAD"])
        .unwrap_or_else(|| "unknown".into());
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
    println!("cargo:rerun-if-changed=build.rs");
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
}
