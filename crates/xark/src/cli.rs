//! `xark` frontend subcommands: `init` (scaffold), `build` (Rust → xark-IR →
//! R1CS) and `check` (editor-facing validation). The backend subcommands
//! (`setup`/`prove`/`verify`/`export`/`ceremony`/`inspect`) live in the
//! [`crate::commands`] module; these three retain their hand-rolled argument
//! parsing (driven from the clap layer in `commands`) because they shell out to
//! `cargo` with a carefully constructed environment.

use std::path::PathBuf;
use std::process::Command;

/// `xark build <crate-dir> [--out DIR] [--field F]`
///
/// Drives `cargo build` on the circuit crate with `xark` itself as `RUSTC`, under
/// one pinned nightly, so every dependency (the `xark` lib + gadget crates) is
/// built with matching MIR-encoded rlibs and only the primary crate is extracted.
pub fn cmd_build(args: &[String]) -> i32 {
    let mut crate_dir: Option<String> = None;
    let mut out: Option<String> = None;
    let mut field = "bn254".to_string();
    let mut it = args.iter();
    while let Some(a) = it.next() {
        match a.as_str() {
            "--out" => out = it.next().cloned(),
            "--field" => {
                if let Some(f) = it.next() {
                    field = f.clone();
                }
            }
            _ if crate_dir.is_none() => crate_dir = Some(a.clone()),
            _ => {}
        }
    }
    let Some(crate_dir) = crate_dir else {
        eprintln!("error: `xark build <crate-dir>` requires a crate directory");
        return 2;
    };
    let crate_dir = PathBuf::from(crate_dir);
    let name = crate_dir
        .file_name()
        .and_then(|s| s.to_str())
        .unwrap_or("circuit")
        .to_string();
    let cwd = std::env::current_dir().expect("cwd");
    let crate_abs = cwd.join(&crate_dir);
    // Everything xark produces lives under the crate's `target/xark/`: the emitted
    // artifacts (circuit.json, r1cs.json) AND an isolated cargo target for the
    // nightly xark-as-rustc build. Isolating the cargo target keeps the nightly /
    // MIR-encoded rlibs from thrashing the crate's normal `target/` — the one your
    // own `cargo` and rust-analyzer use.
    let xark_dir = crate_abs.join("target/xark");
    let out_abs = out.map(|o| cwd.join(o)).unwrap_or_else(|| xark_dir.clone());

    let self_exe = std::env::current_exe().expect("current_exe");
    let toolchain = option_env!("XARK_TOOLCHAIN").unwrap_or("nightly");

    eprintln!("xark: building circuit `{name}` (toolchain {toolchain})");
    let status = Command::new("cargo")
        .arg("build")
        .current_dir(&crate_dir)
        .env("RUSTC", &self_exe)
        .env("RUSTUP_TOOLCHAIN", toolchain)
        .env("CARGO_TARGET_DIR", &xark_dir)
        .env(
            "RUSTFLAGS",
            "--allow=unexpected_cfgs -Zalways-encode-mir -Zmir-opt-level=0",
        )
        .env("XARK_OUT", &out_abs)
        .env("XARK_FIELD", &field)
        .status();

    match status {
        Ok(_) if out_abs.join("circuit.json").exists() => {
            eprintln!("xark: wrote {}", out_abs.display());
            0
        }
        Ok(s) => {
            eprintln!(
                "xark: no circuit.json produced (does the crate expose `pub fn circuit(..)`?); \
                 cargo exit {:?}",
                s.code()
            );
            1
        }
        Err(e) => {
            eprintln!("xark: failed to run cargo: {e}");
            1
        }
    }
}

/// `xark check <crate-dir>`
///
/// Fast, artifact-free validation of a circuit crate for editor diagnostics.
/// Drives `cargo check` with `xark` as `RUSTC` (so gadget deps build with
/// MIR-encoded metadata) and injects `--check` via `RUSTFLAGS`; the driver then
/// validates + lowers the primary crate and routes any rejection through rustc's
/// diagnostic context. `--message-format=json` makes cargo wrap those
/// diagnostics as JSON on stdout — exactly the shape `rust-analyzer`'s
/// `check.overrideCommand` consumes. Exit status mirrors `cargo check`.
pub fn cmd_check(args: &[String]) -> i32 {
    let mut crate_dir: Option<String> = None;
    let mut json = false;
    let mut it = args.iter();
    while let Some(a) = it.next() {
        match a.as_str() {
            // Emit machine-readable JSON diagnostics (for editors / rust-analyzer).
            "--message-format=json" | "--json" => json = true,
            _ if crate_dir.is_none() => crate_dir = Some(a.clone()),
            _ => {}
        }
    }
    let Some(crate_dir) = crate_dir else {
        eprintln!("error: `xark check <crate-dir>` requires a crate directory");
        return 2;
    };
    let crate_dir = PathBuf::from(crate_dir);
    let crate_abs = std::env::current_dir().expect("cwd").join(&crate_dir);

    let self_exe = std::env::current_exe().expect("current_exe");
    let toolchain = option_env!("XARK_TOOLCHAIN").unwrap_or("nightly");

    let mut cmd = Command::new("cargo");
    cmd.arg("check")
        .current_dir(&crate_dir)
        .env("RUSTC", &self_exe)
        .env("RUSTUP_TOOLCHAIN", toolchain)
        // Isolated cargo target (nightly / MIR-encoded rlibs) so on-save checks
        // never invalidate the crate's normal `target/` — the one rust-analyzer's
        // own analysis and your `cargo build` use. This is what makes editor
        // integration fast (no rebuild-on-save thrash).
        .env("CARGO_TARGET_DIR", crate_abs.join("target/xark"))
        // `--check` is injected globally, but only the primary package extracts
        // (see `run_as_rustc`); dependency crates compile normally.
        .env(
            "RUSTFLAGS",
            "--allow=unexpected_cfgs -Zalways-encode-mir -Zmir-opt-level=0 --check",
        );
    if json {
        cmd.arg("--message-format=json");
    }
    match cmd.status() {
        Ok(s) => s.code().unwrap_or(1),
        Err(e) => {
            eprintln!("xark: failed to run cargo: {e}");
            1
        }
    }
}

/// `xark init [name]` — scaffold a ready-to-edit circuit crate, pre-wired for
/// rust-analyzer so unsupported constructs surface inline as you type (via
/// `xark check`). With no name, initializes the current directory.
pub fn cmd_init(args: &[String]) -> i32 {
    let name_arg = args.iter().find(|a| !a.starts_with('-')).cloned();
    let cwd = std::env::current_dir().expect("cwd");
    let (dir, name) = match &name_arg {
        Some(n) => (cwd.join(n), n.clone()),
        None => (
            cwd.clone(),
            cwd.file_name()
                .and_then(|s| s.to_str())
                .unwrap_or("circuit")
                .to_string(),
        ),
    };

    let cargo_toml = format!(
        "[package]\n\
         name = \"{name}\"\n\
         version = \"0.1.0\"\n\
         edition = \"2021\"\n\n\
         [lib]\n\
         crate-type = [\"lib\"]\n\n\
         [dependencies]\n\
         # Once xark is published:  xark = \"0.1\"\n\
         # From git:                xark = {{ git = \"https://github.com/blueshift-gg/xark\", branch = \"lang\", default-features = false }}\n\
         # From a local checkout:   xark = {{ path = \"../xark/crates/xark\", default-features = false }}\n\
         xark = \"0.1\"\n"
    );
    // Both files set the same rust-analyzer override: `rust-analyzer.toml` is the
    // editor-agnostic form; `.vscode/settings.json` covers VS Code specifically.
    let ra_cmd = "[\"xark\", \"check\", \".\", \"--message-format=json\"]";
    let files: [(&str, String); 5] = [
        ("Cargo.toml", cargo_toml),
        ("src/lib.rs", LIB_TEMPLATE.to_string()),
        (
            "rust-analyzer.toml",
            format!(
                "# Run xark's subset validator on save so unsupported constructs show inline.\n\
                 # Needs `xark` on PATH (see `xark init` output). Layers on top of rustc checks.\n\
                 [check]\n\
                 overrideCommand = {ra_cmd}\n"
            ),
        ),
        (
            ".vscode/settings.json",
            format!("{{\n  \"rust-analyzer.check.overrideCommand\": {ra_cmd}\n}}\n"),
        ),
        (".gitignore", "/target\n".to_string()),
    ];

    let mut created = 0u32;
    for (rel, contents) in &files {
        let path = dir.join(rel);
        if path.exists() {
            eprintln!("xark: keeping existing {rel}");
            continue;
        }
        if let Some(parent) = path.parent() {
            if let Err(e) = std::fs::create_dir_all(parent) {
                eprintln!("xark: failed to create {}: {e}", parent.display());
                return 1;
            }
        }
        if let Err(e) = std::fs::write(&path, contents) {
            eprintln!("xark: failed to write {rel}: {e}");
            return 1;
        }
        created += 1;
    }

    eprintln!(
        "xark: scaffolded circuit `{name}` ({created} files) in {}",
        dir.display()
    );
    eprintln!("  1. set the `xark` dependency in Cargo.toml (see its comments)");
    eprintln!("  2. install the CLI so editors can find it:");
    eprintln!("       cargo install --path <xark-repo>/crates/xark --features cli");
    eprintln!(
        "  3. open the folder for live diagnostics, then: xark build . && xark prove target/xark"
    );
    0
}

/// The starter circuit written by `xark init`.
const LIB_TEMPLATE: &str = "\
#![no_std]
use xark::prelude::*;

/// A circuit proves a statement about its inputs without revealing the private
/// ones. `Private<Field>` values form the secret witness; `Public<Field>` values
/// are known to the verifier. `assert_eq` emits an equality *constraint* (not a
/// native `bool`), and `Field` supports `+ - * ^` (with `^ n` = exponentiation).
///
/// Build with `xark build .`; prove with
///   `xark prove target/xark --input secret=3 --input result=9`.
pub fn circuit(secret: Private<Field>, result: Public<Field>) {
    // Prove knowledge of a square root: `secret * secret == result`.
    assert_eq(secret * secret, result);
}
";
