//! `xark doctor` — check the local machine is set up to build and prove
//! circuits, and print the exact fix for anything missing.
//!
//! The `xark build`/`check` path drives `cargo` with `xark` as `RUSTC` under a
//! pinned nightly (with `rustc-dev` / `rust-src` / `llvm-tools`). That toolchain
//! is the single most common thing a newcomer gets wrong, so `doctor` verifies
//! it up front — turning a cryptic mid-build failure into a one-line fix.

use std::process::Command;

use anyhow::Result;
use clap::Args;

#[derive(Args, Debug)]
pub struct DoctorArgs {}

pub fn run(_args: DoctorArgs) -> Result<()> {
    let driver = crate::cli::find_rustc_shim();
    let driver_identity = driver
        .as_ref()
        .and_then(|d| Command::new(d).arg("--print-xark-version").output().ok())
        .filter(|o| o.status.success())
        .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string())
        .filter(|s| !s.is_empty());

    // The driver bakes the exact pinned toolchain. Keep checking the rest of the
    // machine even when it is absent, using the CLI's release-time pin.
    let toolchain_owned = driver
        .as_ref()
        .and_then(|d| Command::new(d).arg("--print-toolchain").output().ok())
        .filter(|o| o.status.success())
        .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string())
        .filter(|s| !s.is_empty())
        .unwrap_or_else(|| env!("XARK_NIGHTLY").to_string());
    let toolchain = toolchain_owned.as_str();
    let channel = channel_of(toolchain);
    let install_tc = format!(
        "rustup toolchain install {channel} --profile minimal \
         --component rust-src --component rustc-dev --component llvm-tools"
    );

    println!(
        "{}",
        crate::style::brand("xark doctor — checking your setup\n")
    );

    let mut problems = 0u32;

    let dirty_source = env!("XARK_GIT_HASH").ends_with("-dirty");
    let source_root = env!("XARK_SOURCE_ROOT");
    let install_cli = if dirty_source && !source_root.is_empty() {
        format!("cargo install --path {source_root}/crates/cli --locked")
    } else {
        format!(
            "cargo install xark-cli --version {} --locked",
            env!("CARGO_PKG_VERSION")
        )
    };
    let install_driver = if dirty_source && !source_root.is_empty() {
        format!(
            "cargo +{} install --path {source_root}/crates/rustc --locked",
            env!("XARK_NIGHTLY")
        )
    } else {
        format!(
            "cargo +{} install xark-rustc --version {} --locked",
            env!("XARK_NIGHTLY"),
            env!("CARGO_PKG_VERSION")
        )
    };
    problems += check(
        driver_identity.is_some(),
        "xark-rustc driver",
        driver.as_ref().and_then(|path| path.to_str()),
        &install_driver,
    );
    let expected_identity = current_identity();
    if let Some(actual) = driver_identity.as_deref() {
        problems += check(
            identities_match(&expected_identity, actual),
            "xark CLI / driver parity",
            Some(actual),
            &format!(
                "reinstall both from the same source: `{install_cli}` then `{install_driver}`",
            ),
        );
    }
    info(
        !dirty_source,
        "reproducible source",
        if dirty_source {
            "init/export will pin local checkout paths"
        } else {
            "CLI identity can be reproduced"
        },
        "commit the Xark source changes before publishing generated manifests",
    );

    // Rust toolchain (required)
    let cargo = cmd_ok("cargo", &["--version"]);
    problems += check(
        cargo.is_some(),
        "cargo",
        cargo.as_deref(),
        "install Rust from https://rustup.rs",
    );

    let rustup = cmd_ok("rustup", &["--version"]);
    problems += check(
        rustup.is_some(),
        "rustup",
        rustup.as_deref(),
        "install Rust from https://rustup.rs",
    );

    let toolchains = cmd_ok("rustup", &["toolchain", "list"]).unwrap_or_default();
    let tc_ok = toolchains
        .lines()
        .any(|l| l.starts_with(toolchain) || l.starts_with(channel.as_str()));
    problems += check(
        tc_ok,
        &format!("toolchain {channel}"),
        tc_ok.then_some(toolchain),
        &install_tc,
    );

    // Toolchain components (required; only checked if the toolchain is present).
    let comps = if tc_ok {
        cmd_ok(
            "rustup",
            &["component", "list", "--toolchain", toolchain, "--installed"],
        )
        .unwrap_or_default()
    } else {
        String::new()
    };
    for comp in ["rustc-dev", "rust-src", "llvm-tools"] {
        // Match a whole component line — `llvm-tools` or a target-suffixed
        // `llvm-tools-<triple>` — not any incidental substring.
        let installed = tc_ok
            && comps
                .lines()
                .any(|l| l.trim() == comp || l.trim().starts_with(&format!("{comp}-")));
        problems += check(
            installed,
            &format!("component {comp}"),
            None,
            &format!("rustup component add {comp} --toolchain {channel}"),
        );
    }

    // Optional (informational — never a hard failure).
    let onpath = cmd_ok("xark", &["--version"]);
    let onpath_matches = onpath
        .as_deref()
        .and_then(|value| value.strip_prefix("xark "))
        .is_some_and(|actual| identities_match(&expected_identity, actual));
    info(
        onpath_matches,
        "xark on PATH",
        "resolves to this CLI build",
        &install_cli,
    );
    let node = cmd_ok("node", &["--version"]);
    info(
        node.is_some(),
        "node",
        "optional — only for the `xark client` TypeScript output",
        "install Node.js from https://nodejs.org",
    );

    println!();
    if problems == 0 {
        let message = if dirty_source {
            "✅ All required checks passed — local build, init, test, and export are ready."
        } else {
            "✅ All required checks passed — you're ready to `xark init`."
        };
        println!("{}", crate::style::brand(message));
    } else {
        println!(
            "{}",
            crate::style::err(&format!(
                "❌ {problems} issue(s) above — fix the ❌ lines, then re-run `xark doctor`."
            ))
        );
        std::process::exit(1);
    }
    Ok(())
}

/// Run `bin args…`; return trimmed stdout on success, `None` on any failure
/// (including the binary not being found).
fn cmd_ok(bin: &str, args: &[&str]) -> Option<String> {
    let out = Command::new(bin).args(args).output().ok()?;
    out.status
        .success()
        .then(|| String::from_utf8_lossy(&out.stdout).trim().to_string())
}

/// Print a required-check line; return `1` if it FAILED (for the problem count).
fn check(ok: bool, label: &str, detail: Option<&str>, fix: &str) -> u32 {
    if ok {
        let d = detail
            .map(|d| format!("  {}", crate::style::dim(d)))
            .unwrap_or_default();
        println!("  {} {label}{d}", crate::style::brand("✅"));
        0
    } else {
        println!("  {} {label}", crate::style::err("❌"));
        println!("       {}", crate::style::dim(&format!("fix: {fix}")));
        1
    }
}

/// Print an optional/informational line — a present ✅ or an amber bullet, but
/// never counted as a failure.
fn info(ok: bool, label: &str, note: &str, fix: &str) {
    if ok {
        println!(
            "  {} {label}  {}",
            crate::style::brand("✅"),
            crate::style::dim(note)
        );
    } else {
        println!(
            "  {} {label}  {}",
            crate::style::warn("•"),
            crate::style::dim(note)
        );
        println!("       {}", crate::style::dim(&format!("fix: {fix}")));
    }
}

/// Reduce a full toolchain name to its rustup channel:
/// `nightly-2026-05-03-aarch64-apple-darwin` → `nightly-2026-05-03`.
fn channel_of(tc: &str) -> String {
    let parts: Vec<&str> = tc.split('-').collect();
    if parts.len() >= 4
        && parts[0] == "nightly"
        && parts[1].len() == 4
        && parts[1].bytes().all(|b| b.is_ascii_digit())
    {
        format!("nightly-{}-{}-{}", parts[1], parts[2], parts[3])
    } else {
        tc.to_string()
    }
}

fn current_identity() -> String {
    format!(
        "{} ({})",
        env!("CARGO_PKG_VERSION"),
        env!("XARK_GIT_HASH_SHORT")
    )
}

fn identities_match(expected: &str, actual: &str) -> bool {
    expected == actual
}

#[cfg(test)]
mod tests {
    use super::{channel_of, identities_match};

    #[test]
    fn extracts_a_pinned_nightly_channel() {
        assert_eq!(
            channel_of("nightly-2026-05-03-aarch64-apple-darwin"),
            "nightly-2026-05-03"
        );
    }

    #[test]
    fn parity_requires_the_same_release_and_revision() {
        assert!(identities_match("0.2.2 (abc123)", "0.2.2 (abc123)"));
        assert!(!identities_match("0.2.2 (abc123)", "0.2.1 (abc123)"));
        assert!(!identities_match("0.2.2 (abc123)", "0.2.2 (def456)"));
    }
}
