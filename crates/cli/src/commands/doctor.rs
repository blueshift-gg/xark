//! `xark doctor` — check the local machine is set up to build and prove
//! circuits, and print the exact fix for anything missing.
//!
//! Building needs only a stable Rust toolchain (1.89+) and its
//! `wasm32-unknown-unknown` standard library (`xark build` adds it with `rustup` on
//! first use).

use std::process::Command;

use anyhow::Result;
use clap::Args;

#[derive(Args, Debug)]
pub struct DoctorArgs {}

/// Oldest `rustc` that builds a circuit (the `xark` crate's `rust-version`).
const MIN_RUSTC: (u32, u32) = (1, 89);

pub fn run(_args: DoctorArgs) -> Result<()> {
    println!(
        "{}",
        crate::style::brand("xark doctor — checking your setup\n")
    );

    let mut problems = 0u32;

    // Rust toolchain (required)
    let cargo = cmd_ok("cargo", &["--version"]);
    problems += check(
        cargo.is_some(),
        "cargo",
        cargo.as_deref(),
        "install Rust from https://rustup.rs",
    );
    let rustc = cmd_ok("rustc", &["--version"]);
    let version = rustc.as_deref().and_then(|v| {
        let mut it = v.split_whitespace().nth(1)?.split('.');
        Some((
            it.next()?.parse::<u32>().ok()?,
            it.next()?.parse::<u32>().ok()?,
        ))
    });
    problems += check(
        version.is_some_and(|v| v >= MIN_RUSTC),
        &format!("rustc {}.{}+", MIN_RUSTC.0, MIN_RUSTC.1),
        rustc.as_deref(),
        "rustup update stable",
    );
    let rustup = cmd_ok("rustup", &["--version"]);
    problems += check(
        rustup.is_some(),
        "rustup",
        rustup.as_deref(),
        "install Rust from https://rustup.rs",
    );
    let targets = cmd_ok("rustup", &["target", "list", "--installed"]).unwrap_or_default();
    info(
        targets
            .lines()
            .any(|l| l.trim() == "wasm32-unknown-unknown"),
        "target wasm32-unknown-unknown",
        "installed automatically on the first `xark build`",
        "rustup target add wasm32-unknown-unknown",
    );

    // Optional (informational — never a hard failure).
    // The `xark` that `cargo test` runs (`$XARK`, else `PATH`) builds with its
    // own version: an older one can't build this release's circuits.
    let from_env = std::env::var("XARK").ok();
    let bin = from_env.clone().unwrap_or_else(|| "xark".to_string());
    let onpath = cmd_ok(&bin, &["--version"]);
    let theirs = onpath.as_deref().and_then(|v| v.split_whitespace().nth(1));
    let label = match &from_env {
        Some(p) => format!("$XARK ({p})"),
        None => "xark on PATH".to_string(),
    };
    match theirs {
        Some(v) if !xark_ir::same_release(v, env!("CARGO_PKG_VERSION")) => {
            let found = onpath.unwrap_or_default();
            info(
                false,
                &label,
                &format!(
                    "is `{found}`, another release than {}: `cargo test` and rust-analyzer would build with it",
                    env!("CARGO_PKG_VERSION")
                ),
                "cargo install xark-cli --force",
            );
        }
        _ => info(
            onpath.is_some(),
            &label,
            "used by rust-analyzer diagnostics, and by `cargo test` to build a missing or out-of-date circuit",
            "cargo install xark-cli",
        ),
    }
    let node = cmd_ok("node", &["--version"]);
    info(
        node.is_some(),
        "node",
        "optional — only for the `xark client` TypeScript output",
        "install Node.js from https://nodejs.org",
    );

    println!();
    if problems == 0 {
        println!(
            "{}",
            crate::style::brand("✅ All required checks passed — you're ready to `xark init`.")
        );
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
