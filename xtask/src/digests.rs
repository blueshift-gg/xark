//! `cargo xtask digests`: every example circuit, built by the stable frontend, and its
//! R1CS digest (`stream_digest`), one `<example> <digest>` line each.
//!
//! The digest is the same on every supported rustc (1.89+): the stable frontend's
//! reproducibility guarantee. An example with Rust client functions (`#[input]` on
//! an `impl`) also builds its `client.wasm`, which must build on that rustc too. A difference means a toolchain changed a circuit (a
//! bug to report) or the lowering changed on purpose (`--update`, and review).

use std::collections::BTreeMap;
use std::process::Command;
use std::sync::Mutex;

use anyhow::{Context, Result, bail};

#[derive(clap::Args)]
pub struct Args {
    /// Compare with tests/stable-digests.txt; fail on a difference.
    #[arg(long, conflicts_with = "update")]
    check: bool,
    /// Rewrite tests/stable-digests.txt.
    #[arg(long)]
    update: bool,
    /// Build the circuits with this installed toolchain (`1.89`, `beta`, …) instead
    /// of the workspace's. This tool itself always builds with the workspace's.
    #[arg(long)]
    toolchain: Option<String>,
    /// Circuits built at once.
    #[arg(long, default_value_t = crate::default_jobs())]
    jobs: usize,
}

pub fn run(args: Args) -> Result<()> {
    let rustc = match &args.toolchain {
        Some(t) => use_toolchain(t)?,
        None => "rustc".into(),
    };
    let version = String::from_utf8(Command::new(&rustc).arg("--version").output()?.stdout)?
        .trim()
        .to_string();
    let target = crate::target_dir()
        .join("stable-digests")
        .join(version.replace(' ', "_"));
    let digests = Mutex::new(BTreeMap::new());
    let clients = Mutex::new(Vec::new());
    crate::parallel(crate::circuits()?, args.jobs, |name| {
        let dir = crate::root().join("examples").join(&name);
        let digest = digest(&dir, &target.join(&name)).unwrap_or_else(|e| {
            eprintln!("{name}: {e}");
            "BUILD-FAILED".into()
        });
        if has_client_functions(&dir) {
            let built = xark_frontend::build_client(&dir, &target.join(&name).join("client"));
            clients.lock().unwrap().push((name.clone(), built.err()));
        }
        digests.lock().unwrap().insert(name, digest);
    });
    let text: String = digests
        .into_inner()
        .unwrap()
        .into_iter()
        .map(|(n, d)| format!("{n} {d}\n"))
        .collect();
    let want = crate::root().join("tests/stable-digests.txt");
    let count = text.lines().count();
    if args.update {
        std::fs::write(&want, &text)?;
        println!("wrote {} ({count} circuits)", want.display());
    } else if args.check {
        let old = std::fs::read_to_string(&want)
            .with_context(|| format!("reading {}", want.display()))?;
        let differ: Vec<String> = diff(&old, &text);
        if !differ.is_empty() {
            bail!(
                "circuit digests differ under {version}:\n{}",
                differ.join("\n")
            );
        }
        println!("all {count} circuits match ({version})");
    } else {
        print!("{text}");
    }
    let clients = clients.into_inner().unwrap();
    let failed: Vec<String> = clients
        .iter()
        .filter_map(|(n, e)| e.as_ref().map(|e| format!("{n}: {e}")))
        .collect();
    if !failed.is_empty() {
        bail!(
            "client.wasm doesn't build under {version}:\n{}",
            failed.join("\n")
        );
    }
    eprintln!("{} client.wasm build ({version})", clients.len());
    Ok(())
}

/// Whether the crate at `dir` puts `#[input]` on an `impl`: it has Rust functions a
/// generated client calls, built as `client.wasm`.
fn has_client_functions(dir: &std::path::Path) -> bool {
    let src = std::fs::read_to_string(dir.join("src/lib.rs")).unwrap_or_default();
    let lines: Vec<&str> = src.lines().map(str::trim).collect();
    lines.windows(2).any(|w| {
        matches!(w[0], "#[input]" | "#[xark::input]")
            && (w[1].starts_with("impl ") || w[1].starts_with("impl<"))
    })
}

/// Build the circuit crate at `dir` and digest its R1CS, after checking the compact
/// artifact expands to exactly the flat lowering.
fn digest(dir: &std::path::Path, target: &std::path::Path) -> Result<String> {
    let wasm = xark_frontend::build_crate(dir, target).map_err(|e| anyhow::anyhow!("{e}"))?;
    let out = xark_frontend::lower_module(&wasm, xark_ir::FieldSpec::named("bn254"), false, false)
        .map_err(|e| anyhow::anyhow!("{e}"))?
        .output;
    xark_ir::function_decode::verify_blob_matches(&out.xbc, &out.r1cs, &out.primitive)
        .map_err(|e| anyhow::anyhow!("circuit.xbc doesn't match the flat lowering: {e}"))?;
    Ok(format!(
        "{:032x}",
        xark_ir::function_decode::stream_digest(&out.xbc)
    ))
}

/// Make every circuit build use toolchain `t`: the frontend runs `$CARGO`, which
/// runs `$RUSTC`, and a bare `rustc` (its sysroot check) goes through rustup.
/// Returns that toolchain's `rustc`.
fn use_toolchain(t: &str) -> Result<String> {
    let which = |tool: &str| -> Result<String> {
        let out = Command::new("rustup")
            .args(["which", tool, "--toolchain", t])
            .output()?;
        if !out.status.success() {
            bail!(
                "toolchain {t} isn't installed (`rustup toolchain install {t} --target wasm32-unknown-unknown`)"
            );
        }
        Ok(String::from_utf8(out.stdout)?.trim().to_string())
    };
    let (cargo, rustc) = (which("cargo")?, which("rustc")?);
    // SAFETY: set before any thread starts.
    unsafe {
        std::env::set_var("RUSTUP_TOOLCHAIN", t);
        std::env::set_var("CARGO", &cargo);
        std::env::set_var("RUSTC", &rustc);
    }
    Ok(rustc)
}

/// The lines of `want` and `got` that differ, as `-` / `+` lines.
fn diff(want: &str, got: &str) -> Vec<String> {
    let parse = |s: &str| -> BTreeMap<String, String> {
        s.lines()
            .filter_map(|l| l.split_once(' '))
            .map(|(n, d)| (n.to_string(), d.to_string()))
            .collect()
    };
    let (want, got) = (parse(want), parse(got));
    let mut out = Vec::new();
    for name in want
        .keys()
        .chain(got.keys().filter(|n| !want.contains_key(*n)))
    {
        match (want.get(name), got.get(name)) {
            (Some(a), Some(b)) if a == b => {}
            (a, b) => {
                if let Some(a) = a {
                    out.push(format!("- {name} {a}"));
                }
                if let Some(b) = b {
                    out.push(format!("+ {name} {b}"));
                }
            }
        }
    }
    out
}
