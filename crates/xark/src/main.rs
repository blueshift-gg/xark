//! `xark`: the toolchain binary — both the friendly CLI (`xark build|prove`) and,
//! when cargo invokes it as `RUSTC` during `xark build`, the `rustc_driver` that
//! extracts each circuit's R1CS.
//!
//! ```text
//! xark build <crate-dir> [--out <dir>] [--field <name>]
//! xark prove <out-dir>   [--input <name>=<value>]...
//! ```
//!
//! `xark build` runs `cargo build` on the circuit crate with this binary as
//! `RUSTC` under one pinned nightly, so cargo builds every dependency (the `xark`
//! lib and any gadget crates) with matching MIR-encoded rlibs; we extract only
//! the primary crate (cargo sets `CARGO_PRIMARY_PACKAGE`) and compile the rest
//! normally.

#![feature(rustc_private)]

extern crate rustc_abi;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_span;

mod cli;
mod commands;
mod diagnostics;
mod driver;
mod find_entry;
mod lower_mir;
mod validate;
mod xark_project;

use std::path::PathBuf;

use driver::R1csCallbacks;

/// The clap-driven CLI subcommands (plus clap's own help/version flags). When
/// `args[1]` is one of these, `xark` behaves as the user-facing toolchain and
/// parses with clap; otherwise it was invoked as `RUSTC` (by cargo during
/// `xark build`, or directly with rustc arguments) and drives `rustc_driver`.
const CLI_SUBCOMMANDS: &[&str] = &[
    "init",
    "new",
    "build",
    "check",
    "setup",
    "prove",
    "verify",
    "export",
    "ceremony",
    "inspect",
    "completions",
    "help",
    "-h",
    "--help",
    "-V",
    "--version",
];

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let is_cli = args
        .get(1)
        .map(String::as_str)
        .is_some_and(|a| CLI_SUBCOMMANDS.contains(&a));
    if is_cli {
        // The clap CLI owns the process from here (it calls `std::process::exit`
        // on error / for completions). clap re-reads `std::env::args` itself.
        commands::main();
    } else {
        // Invoked as `RUSTC` (by cargo, during `xark build`) or directly with
        // rustc arguments. The snapshot harness depends on this direct path.
        run_as_rustc(args);
    }
}

/// `rustc_driver` entry. Extract the circuit's R1CS when an output directory is
/// requested — either directly via `--r1cs-out <dir>` / `--field <name>` (the
/// snapshot test harness) or, under `cargo` (`xark build`), for the primary
/// package via `XARK_OUT`/`CARGO_PRIMARY_PACKAGE`. Dependency crates compile
/// normally so their MIR-encoded rlibs exist for cross-crate inlining.
fn run_as_rustc(mut args: Vec<String>) {
    // Direct-invocation flags (`--r1cs-out`, `--field`, `--check`) — stripped
    // before rustc.
    let (direct_out, direct_field, check) = strip_xark_flags(&mut args);
    ensure_sysroot(&mut args);

    let is_build_script = args
        .windows(2)
        .any(|w| w[0] == "--crate-name" && w[1].starts_with("build_script"));
    let is_primary = std::env::var_os("CARGO_PRIMARY_PACKAGE").is_some();
    let cargo_out = is_primary.then(|| std::env::var("XARK_OUT").ok()).flatten();
    let out = direct_out.or(cargo_out);
    // `--check` runs the extractor purely for diagnostics (no output dir needed).
    // Under cargo it is injected globally via RUSTFLAGS, so restrict extraction
    // to the primary package — dependency crates (the `xark` lib, gadget crates)
    // have no `circuit` fn and must compile normally. Outside cargo (direct
    // driver invocation) `CARGO` is unset, so honor `--check` unconditionally.
    let under_cargo = std::env::var_os("CARGO").is_some();
    let check_here = check && (is_primary || !under_cargo);
    let extract = !is_build_script && (check_here || out.is_some());

    let result = if extract {
        let field = direct_field
            .or_else(|| std::env::var("XARK_FIELD").ok())
            .map(|n| xark_ir::FieldSpec::named(&n))
            .unwrap_or_else(xark_ir::FieldSpec::unknown);
        let mut cb = R1csCallbacks {
            output_dir: out.map(PathBuf::from).unwrap_or_default(),
            field,
            check_only: check_here,
        };
        rustc_driver::catch_fatal_errors(|| rustc_driver::run_compiler(&args, &mut cb))
    } else {
        let mut cb = PassThrough;
        rustc_driver::catch_fatal_errors(|| rustc_driver::run_compiler(&args, &mut cb))
    };
    if result.is_err() {
        std::process::exit(1);
    }
}

/// No-op callbacks: an ordinary compile that produces the crate's rlib.
struct PassThrough;
impl rustc_driver::Callbacks for PassThrough {}

/// Strip the tool's own flags (`--r1cs-out <dir>`, `--field <name>`, in both
/// `X Y` and `X=Y` forms, and the boolean `--check`) from a rustc argument
/// vector, returning their values.
fn strip_xark_flags(args: &mut Vec<String>) -> (Option<String>, Option<String>, bool) {
    let mut out = None;
    let mut field = None;
    let mut check = false;
    let mut kept = Vec::with_capacity(args.len());
    let mut it = std::mem::take(args).into_iter();
    while let Some(a) = it.next() {
        if a == "--r1cs-out" {
            out = it.next();
        } else if let Some(v) = a.strip_prefix("--r1cs-out=") {
            out = Some(v.to_string());
        } else if a == "--field" {
            field = it.next();
        } else if let Some(v) = a.strip_prefix("--field=") {
            field = Some(v.to_string());
        } else if a == "--check" {
            check = true;
        } else {
            kept.push(a);
        }
    }
    *args = kept;
    (out, field, check)
}

/// Point `--sysroot` at the nightly the `xark` binary was built with (embedded by
/// `build.rs`), independent of the ambient toolchain where `xark` is run.
fn ensure_sysroot(args: &mut Vec<String>) {
    let has = args
        .iter()
        .any(|a| a == "--sysroot" || a.starts_with("--sysroot="));
    if !has {
        if let Some(sysroot) = option_env!("XARK_SYSROOT") {
            args.push("--sysroot".to_string());
            args.push(sysroot.to_string());
        }
    }
}
