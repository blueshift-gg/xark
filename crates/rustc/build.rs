//! Capture the toolchain the `xark` binary is built with, so the CLI can drive
//! `cargo`/the rustc-driver with the *same* nightly (sysroot + toolchain),
//! independent of the ambient toolchain where `xark build` is later run.
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
    let git_hash = git(&["rev-parse", "--short=12", "HEAD"]).unwrap_or_else(|| "unknown".into());
    println!("cargo:rustc-env=XARK_GIT_HASH={git_hash}");
    println!("cargo:rerun-if-changed=build.rs");

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
