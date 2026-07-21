//! `xark` frontend subcommands: `init` (scaffold), `build` (Rust → xark-IR →
//! R1CS) and `check` (editor-facing validation). The backend subcommands
//! (`setup`/`prove`/`verify`/`export`/`ceremony`/`inspect`) live in the
//! [`crate::commands`] module; these three retain their hand-rolled argument
//! parsing (driven from the clap layer in `commands`) because they shell out to
//! `cargo` with a carefully constructed environment.

use std::path::PathBuf;
use std::process::Command;

/// Locate the `xark-rustc` binary — the `rustc_driver` shim — without failing.
/// Honors the `XARK_RUSTC` env var (an explicit path override, used by the test
/// harness which builds the driver separately); otherwise it's a sibling of the
/// `xark` CLI (same dir). `None` if neither is present. The driver lives in a
/// separate binary so the CLI can host a fast global allocator and stay on stable
/// Rust; `xark build`/`check` invoke it as `RUSTC`.
pub(crate) fn find_rustc_shim() -> Option<PathBuf> {
    if let Some(path) = std::env::var_os("XARK_RUSTC") {
        return Some(PathBuf::from(path));
    }
    let self_exe = std::env::current_exe().ok()?;
    self_exe
        .parent()
        .map(|dir| dir.join(format!("xark-rustc{}", std::env::consts::EXE_SUFFIX)))
        .filter(|p| p.exists())
}

/// Locate the `xark-rustc` driver, or panic with a reinstall hint.
fn rustc_shim() -> PathBuf {
    find_rustc_shim().unwrap_or_else(|| {
        panic!(
            "xark-rustc not found next to the `xark` binary (or set XARK_RUSTC) — install \
             it: `cargo +nightly-2026-05-03 install --git https://github.com/blueshift-gg/xark xark-rustc`"
        )
    })
}

/// `xark build <crate-dir> [--out DIR] [--field F]`
///
/// Drives `cargo build` on the circuit crate with `xark` itself as `RUSTC`, under
/// one pinned nightly, so every dependency (the `xark` lib + gadget crates) is
/// built with matching MIR-encoded rlibs and only the primary crate is extracted.
pub fn cmd_build(args: &[String]) -> i32 {
    cmd_build_impl(args, false)
}

/// Like [`cmd_build`], but injects `--profile` so the extractor additionally
/// writes `profile.json` (per-constraint source/function/kind attribution). Used
/// by `xark profile`; a normal `xark build` never emits it.
pub fn cmd_build_profile(args: &[String]) -> i32 {
    cmd_build_impl(args, true)
}

fn cmd_build_impl(args: &[String], profile: bool) -> i32 {
    let mut crate_dir: Option<String> = None;
    let mut out: Option<String> = None;
    let mut field = "bn254".to_string();
    // `--emit-json`: also write the human-readable `circuit.json`. Off by default
    // — the prover/checker load `circuit.xbc` instead, so a normal build skips the
    // (multi-GB on large circuits) primitive-program JSON serialization.
    let mut emit_json = false;
    let mut it = args.iter();
    while let Some(a) = it.next() {
        match a.as_str() {
            "--out" => out = it.next().cloned(),
            "--field" => {
                if let Some(f) = it.next() {
                    field = f.clone();
                }
            }
            "--emit-json" => emit_json = true,
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
    //
    // The cargo build cache stays at the shared `target/xark/` (so all circuits in
    // a workspace share compiled deps), but each circuit's *artifacts* land in a
    // name-scoped subdir `target/xark/<pkg-name>/` for per-circuit isolation. The
    // package name comes from the crate's `Cargo.toml` (`[package] name`), falling
    // back to the directory name.
    let xark_dir = crate_abs.join("target/xark");
    let pkg_name = crate::xark_project::read_pkg_name(&crate_abs).unwrap_or_else(|| name.clone());
    let out_abs = out
        .map(|o| cwd.join(o))
        .unwrap_or_else(|| xark_dir.join(&pkg_name));

    let self_exe = rustc_shim();

    // The emitted artifacts are a side-effect of compilation. If they were
    // deleted but the source is unchanged, cargo cache-hits and never re-runs the
    // extractor, so they never come back. Bump the source mtime to force the
    // primary crate to recompile when the output looks incomplete — but only
    // then. `circuit.xbc` is the artifact every build writes, so its absence is
    // the primary "needs (re)build" signal.
    let regen_needed = !out_abs.join("circuit.xbc").exists()
        // `--emit-json` needs circuit.json / r1cs.json; force a recompile if they
        // are absent so a circuit already built without them gets the JSON when
        // re-requested.
        || (emit_json
            && (!out_abs.join("circuit.json").exists() || !out_abs.join("r1cs.json").exists()))
        // `xark profile` needs profile.json; force a recompile if it's absent so
        // an already-built (cache-hit) circuit still produces the attribution.
        || (profile && !out_abs.join("profile.json").exists());
    if regen_needed {
        touch_sources(&crate_abs);
    }

    let target_dir = std::env::var_os("CARGO_TARGET_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| xark_dir.clone());
    eprintln!("{} building circuit `{name}`", crate::style::tag());
    // `--profile` / `--emit-json` (when requested) are injected globally, but
    // only the primary package extracts (see `run_as_rustc`), so dependency
    // crates ignore them.
    let mut rustflags =
        String::from("--allow=unexpected_cfgs -Zalways-encode-mir -Zmir-opt-level=0");
    if profile {
        rustflags.push_str(" --profile");
    }
    if emit_json {
        rustflags.push_str(" --emit-json");
    }
    // Heartbeat: large circuits lower for a long time with no output (ed25519 is
    // ~2min), which reads as a hang. A watcher thread prints an "still building"
    // line every 15s; it exits promptly when the build finishes (tx drop). Builds
    // under 15s never print anything.
    let (tx, rx) = std::sync::mpsc::channel::<()>();
    let heartbeat = std::thread::spawn(move || {
        let start = std::time::Instant::now();
        while let Err(std::sync::mpsc::RecvTimeoutError::Timeout) =
            rx.recv_timeout(std::time::Duration::from_secs(15))
        {
            eprintln!(
                "{} still building… ({}s; large circuits take a while — RUST_LOG=debug for detail)",
                crate::style::tag(),
                start.elapsed().as_secs()
            );
        }
    });
    let status = Command::new("cargo")
        .arg("build")
        .current_dir(&crate_dir)
        // No `RUSTUP_TOOLCHAIN`: `xark-rustc` is a self-contained rustc_driver that
        // resolves its own (pinned-nightly) sysroot via a baked rpath, so cargo can
        // run under the user's ambient (stable) toolchain with it as `RUSTC`.
        .env("RUSTC", &self_exe)
        .env("CARGO_TARGET_DIR", &target_dir)
        .env("RUSTFLAGS", rustflags)
        .env("XARK_OUT", &out_abs)
        .env("XARK_FIELD", &field)
        .status();
    drop(tx);
    let _ = heartbeat.join();

    match status {
        Ok(_) if out_abs.join("circuit.xbc").exists() => {
            eprintln!(
                "{} wrote {}",
                crate::style::tag(),
                crate::style::brand(&out_abs.display().to_string())
            );
            eprintln!(
                "\n{}",
                crate::style::next_steps(&[(
                    format!("xark setup {}", crate_dir.display()),
                    "generate the proving/verifying keys",
                )])
            );
            0
        }
        Ok(s) => {
            eprintln!(
                "xark: no circuit.xbc produced (does the crate expose `pub fn circuit(..)`?); \
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

/// Bump the mtime of the crate's `src/*.rs` files so cargo recompiles the primary
/// crate on the next build (forcing the extractor to re-emit artifacts).
/// Best-effort: per-file failures are ignored. Content is never modified.
fn touch_sources(crate_dir: &std::path::Path) {
    fn walk(dir: &std::path::Path, now: std::time::SystemTime) {
        let Ok(entries) = std::fs::read_dir(dir) else {
            return;
        };
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                walk(&path, now);
            } else if path.extension().is_some_and(|e| e == "rs") {
                if let Ok(f) = std::fs::File::options().write(true).open(&path) {
                    let _ = f.set_modified(now);
                }
            }
        }
    }
    walk(&crate_dir.join("src"), std::time::SystemTime::now());
}

/// `xark clean` — remove **every** xark output tree under the current directory:
/// each circuit crate's `target/xark/` (emitted artifacts, keys, proofs, and the
/// isolated cargo target). Takes no arguments.
pub fn cmd_clean(_args: &[String]) -> i32 {
    fn walk(dir: &std::path::Path, removed: &mut u32, errors: &mut u32) {
        let Ok(entries) = std::fs::read_dir(dir) else {
            return;
        };
        for entry in entries.flatten() {
            let path = entry.path();
            if !path.is_dir() {
                continue;
            }
            match path.file_name().and_then(|s| s.to_str()) {
                // Remove `target/xark` here; don't descend into `target/` itself.
                Some("target") => {
                    let xark = path.join("xark");
                    if xark.is_dir() {
                        match std::fs::remove_dir_all(&xark) {
                            Ok(()) => {
                                eprintln!("xark: removed {}", xark.display());
                                *removed += 1;
                            }
                            Err(e) => {
                                eprintln!("xark: failed to remove {}: {e}", xark.display());
                                *errors += 1;
                            }
                        }
                    }
                }
                Some(".git") => {} // skip VCS noise
                _ => walk(&path, removed, errors),
            }
        }
    }
    let root = std::env::current_dir().expect("cwd");
    let (mut removed, mut errors) = (0u32, 0u32);
    walk(&root, &mut removed, &mut errors);
    if removed == 0 && errors == 0 {
        eprintln!(
            "xark: nothing to clean (no target/xark under {})",
            root.display()
        );
    } else {
        eprintln!(
            "xark: cleaned {removed} target/xark director{}",
            if removed == 1 { "y" } else { "ies" }
        );
    }
    (errors > 0) as i32
}

/// `xark test [crate-dir] [-- <cargo test args>]`
///
/// One-shot circuit testing: build the crate (`xark build`) so its
/// `target/xark/<pkg>/` artifacts exist, then run `cargo test` in the crate so
/// the in-crate `xark_prover::circuit(..).check(..)` tests can load them.
pub fn cmd_test(args: &[String]) -> i32 {
    // Split at `--`: everything before is ours (the crate dir); everything
    // after is forwarded verbatim to `cargo test`.
    let (ours, forwarded): (&[String], &[String]) = match args.iter().position(|a| a == "--") {
        Some(i) => (&args[..i], &args[i + 1..]),
        None => (args, &[]),
    };
    let crate_dir = ours
        .iter()
        .find(|a| !a.starts_with('-'))
        .cloned()
        .unwrap_or_else(|| ".".to_string());

    // Build first so the artifacts the tests load are present + up to date.
    // Build *with* `--profile` (it also writes `profile.json`, leaving
    // `circuit.json` / `r1cs.json` byte-identical): the `xark_prover` test
    // harness reads it to explain *which* source line / function a failing
    // constraint came from when `c.check(..)` fails.
    let code = cmd_build_profile(std::slice::from_ref(&crate_dir));
    if code != 0 {
        eprintln!("xark: build failed; skipping tests");
        return code;
    }

    // Run in `--release`: circuit tests drive a full Groth16 setup+prove+verify,
    // which is 10–50× slower in debug — a large hash/EC circuit takes *minutes*
    // unoptimized versus seconds optimized. Proving is the whole point of a
    // circuit test, so release is the sensible default (the same reason CI runs
    // these `--release`). Anything after `--` still forwards to the test harness.
    eprintln!("xark: running `cargo test --release` in {crate_dir}");
    let status = Command::new("cargo")
        .arg("test")
        .arg("--release")
        .args(forwarded)
        .current_dir(&crate_dir)
        .status();
    match status {
        Ok(s) => s.code().unwrap_or(1),
        Err(e) => {
            eprintln!("xark: failed to run cargo test: {e}");
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
    for a in args.iter() {
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

    let self_exe = rustc_shim();

    let mut cmd = Command::new("cargo");
    cmd.arg("check")
        .current_dir(&crate_dir)
        // No `RUSTUP_TOOLCHAIN`: the driver self-resolves its nightly sysroot (see
        // `run_build`), so cargo runs under the ambient toolchain.
        .env("RUSTC", &self_exe)
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
         # From git:                
         xark = {{ git = \"https://github.com/blueshift-gg/xark\", default-features = false }}\n\
         # From a local checkout:   xark = {{ path = \"../xark/crates/lang\", default-features = false }}\n\
         # xark = \"0.1\"\n\n\
         # `xark-prover` powers the in-crate `cargo test` circuit tests below.\n\
         [dev-dependencies]\n\
         # Once xark is published:  xark-prover = \"0.1\"\n\
         # From git:                
         xark-prover = {{ git = \"https://github.com/blueshift-gg/xark\" }}\n\
         # From a local checkout:   xark-prover = {{ path = \"../xark/crates/prover\" }}\n\
         # xark-prover = \"0.1\"\n"
    );
    let fn_ident = ident_of(&name);
    let inputs_struct = format!("{}Inputs", pascal_of(&fn_ident));
    let lib_rs = format!(
        "{}{}",
        LIB_TEMPLATE.replace("__FN__", &fn_ident),
        tests_template(&name, &inputs_struct)
    );
    // Both files set the same rust-analyzer override: `rust-analyzer.toml` is the
    // editor-agnostic form; `.vscode/settings.json` covers VS Code specifically.
    let ra_cmd = "[\"xark\", \"check\", \".\", \"--message-format=json\"]";
    let files: [(&str, String); 5] = [
        ("Cargo.toml", cargo_toml),
        ("src/lib.rs", lib_rs),
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
    let where_ = if name_arg.is_some() {
        name.as_str()
    } else {
        "."
    };
    eprintln!("  1. set the `xark` dependency in Cargo.toml (see its comments)");
    eprintln!("  2. install the CLI so editors can find it:");
    eprintln!(
        "       cargo +nightly-2026-05-03 install --path <xark-repo>/crates/lang --features cli"
    );
    eprintln!(
        "\n{}",
        crate::style::next_steps(&[
            (
                format!("xark build {where_}"),
                "compile the circuit to R1CS"
            ),
            (
                format!("xark setup {where_}"),
                "generate the proving/verifying keys"
            ),
            (
                format!("xark prove {where_} --inputs '{{\"secret\": 3, \"result\": 9}}'"),
                "produce your first proof",
            ),
        ])
    );
    0
}

/// Turn a crate name into a valid Rust identifier for the scaffolded entry fn
/// (`my-circuit` → `my_circuit`); falls back to `circuit`.
fn ident_of(name: &str) -> String {
    let mut s: String = name
        .chars()
        .map(|c| if c.is_ascii_alphanumeric() { c } else { '_' })
        .collect();
    if s.is_empty() {
        return "circuit".to_string();
    }
    if s.starts_with(|c: char| c.is_ascii_digit()) {
        s.insert(0, '_');
    }
    s
}

/// `my_square` → `MySquare` — must match `xark-macros`' struct naming so the
/// scaffolded test references the generated `<Fn>Inputs` struct correctly.
fn pascal_of(ident: &str) -> String {
    ident
        .split('_')
        .filter(|seg| !seg.is_empty())
        .map(|seg| {
            let mut chars = seg.chars();
            match chars.next() {
                Some(first) => first.to_ascii_uppercase().to_string() + chars.as_str(),
                None => String::new(),
            }
        })
        .collect()
}

/// The starter circuit written by `xark init`. The `#[cfg(test)] mod tests`
/// block ([`tests_template`]) is appended with the crate's own name filled in.
///
/// `no_std` applies to the real circuit build (via `xark build`) but is dropped
/// under `cargo test` so the `xark-prover` test harness (which uses `std`) can
/// link.
const LIB_TEMPLATE: &str = "\
#![cfg_attr(not(test), no_std)]
use xark::prelude::*;

#[circuit]
pub fn __FN__(secret: Private<Field>, result: Public<Field>) {
    // prove knowledge of a square root: secret * secret == result
    require_eq(secret * secret, result);
}
";

/// The `#[cfg(test)] mod tests` appended to the scaffolded `src/lib.rs`.
///
/// Inputs are the typed struct `#[circuit]` generates from the entry signature
/// (`inputs` = `<Fn>Inputs`), so they're named, not positional. These tests load
/// the built artifacts, so they need `xark build .` to have run first.
fn tests_template(name: &str, inputs: &str) -> String {
    format!(
        "\n\
         #[cfg(test)]\n\
         mod tests {{\n\
         \x20   use super::*;\n\
         \n\
         \x20   #[test]\n\
         \x20   fn accepts_valid() {{\n\
         \x20       let c = xark_prover::circuit(\"{name}\");\n\
         \x20       c.check({inputs} {{ secret: \"2\".into(), result: \"4\".into() }}).unwrap(); // 2 * 2 == 4\n\
         \x20   }}\n\
         \n\
         \x20   #[test]\n\
         \x20   fn rejects_invalid() {{\n\
         \x20       let c = xark_prover::circuit(\"{name}\");\n\
         \x20       assert!(c.check({inputs} {{ secret: \"3\".into(), result: \"4\".into() }}).is_err()); // 3 * 3 != 4\n\
         \x20   }}\n\
         }}\n"
    )
}
