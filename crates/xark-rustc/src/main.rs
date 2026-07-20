//! `xark-rustc`: the `rustc_driver` half of the toolchain — a `RUSTC` shim.
//!
//! `xark build` runs `cargo build` on the circuit crate with **this** binary as
//! `RUSTC` under one pinned nightly, so cargo builds every dependency with
//! matching MIR-encoded rlibs; we extract only the primary crate (cargo sets
//! `CARGO_PRIMARY_PACKAGE`) and compile the rest normally.
//!
//! This is a separate binary from the `xark` CLI precisely because a
//! `rustc_driver` process cannot host a custom `#[global_allocator]` (it aborts
//! at runtime), whereas the CLI wants a fast per-thread allocator for circuit
//! loading. Splitting them lets each use the allocator it needs.

#![feature(rustc_private)]

extern crate rustc_abi;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_span;

mod diagnostics;
mod driver;
mod find_entry;
mod lower_mir;
// Shared with the CLI binary, which uses the full surface; the driver uses only
// a few helpers (e.g. `tag`), so the rest is legitimately unused here.
#[allow(dead_code)]
mod style;
mod validate;

use std::path::PathBuf;

use driver::R1csCallbacks;

/// Developer-diagnostics env-flag probe. Only reads the environment under the
/// `debug` feature; a normal release build compiles this to `false` so the
/// diagnostic branches (timing, faithfulness gate) vanish entirely.
#[inline]
pub(crate) fn dbg_flag(name: &str) -> bool {
    #[cfg(feature = "debug")]
    {
        std::env::var(name).is_ok()
    }
    #[cfg(not(feature = "debug"))]
    {
        let _ = name;
        false
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    // `xark doctor` queries the driver for the exact toolchain it was built
    // against (baked by `build.rs`) — the single source of truth for the pinned
    // nightly. A custom flag cargo never passes when invoking us as `RUSTC`.
    if args.get(1).map(String::as_str) == Some("--print-toolchain") {
        println!("{}", option_env!("XARK_TOOLCHAIN").unwrap_or("nightly"));
        return;
    }
    run_as_rustc(args);
}

/// `rustc_driver` entry. Extract the circuit's R1CS when an output directory is
/// requested — either directly via `--r1cs-out <dir>` / `--field <name>` (the
/// snapshot test harness) or, under `cargo` (`xark build`), for the primary
/// package via `XARK_OUT`/`CARGO_PRIMARY_PACKAGE`. Dependency crates compile
/// normally so their MIR-encoded rlibs exist for cross-crate inlining.
fn run_as_rustc(mut args: Vec<String>) {
    // Direct-invocation flags (`--r1cs-out`, `--field`, `--check`, `--profile`,
    // `--emit-json`) — stripped before rustc.
    let (direct_out, direct_field, check, profile, emit_json) = strip_xark_flags(&mut args);
    ensure_sysroot(&mut args);
    // Report a distinguishing `xark` cfg on *every* invocation — including the
    // `--print cfg` target query cargo runs before building. That lets a circuit
    // crate key `#[cfg(xark)]` on "compiled by the xark toolchain" (e.g.
    // `#![cfg_attr(xark, no_std)]`, host-only code behind `#[cfg(not(xark))]`) AND
    // lets Cargo gate host-only deps via `[target.'cfg(not(xark))'.dependencies]` —
    // together replacing the per-crate `host` feature + the `no_std` ceremony.
    args.push("--cfg".to_string());
    args.push("xark".to_string());

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
            // Emit `profile.json` only in a real build (not `--check`, which
            // writes no artifacts) and only for the extracted primary crate.
            profile: profile && !check_here,
            emit_json,
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
/// `X Y` and `X=Y` forms, and the booleans `--check` / `--profile` /
/// `--emit-json`) from a rustc argument vector, returning their values.
fn strip_xark_flags(args: &mut Vec<String>) -> (Option<String>, Option<String>, bool, bool, bool) {
    let mut out = None;
    let mut field = None;
    let mut check = false;
    let mut profile = false;
    let mut emit_json = false;
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
        } else if a == "--profile" {
            profile = true;
        } else if a == "--emit-json" {
            emit_json = true;
        } else {
            kept.push(a);
        }
    }
    *args = kept;
    (out, field, check, profile, emit_json)
}

/// Point `--sysroot` at the nightly the binary was built with (embedded by
/// `build.rs`), independent of the ambient toolchain where it is run.
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
