//! `cargo xtask digests`: every example circuit, built by the stable frontend, and
//! the digest of the rows its Groth16 keys are made for ([`keyed_digest`]), one
//! `<example> <digest>` line each.
//!
//! The digest is the same on every supported rustc (1.89+): the stable frontend's
//! reproducibility guarantee. An example with Rust client functions (`#[input]` on
//! an `impl`) also builds its `client.wasm`, which must build on that rustc too. A difference means a toolchain changed a circuit (a
//! bug to report) or the lowering or a minimizer changed on purpose (`--update`, and
//! review).
//!
//! # Keyed-rows digest, version 1
//!
//! SHA-256 of the bytes below. Integers are little-endian; `fe` is a field element
//! reduced into `[0, p)`, little-endian, in exactly `⌈bits(p)/8⌉` bytes (32 for
//! BN254). Any rewrite (e.g. for speed) must produce these bytes exactly.
//!
//! ```text
//! b"xark keyed rows v1"
//! u32 len ‖ modulus p in ASCII decimal
//! form(reduced)     the template-reduced rows: what a `reduced` key streams from
//!                   circuit.xbc (expand_function_blob_reduced)
//! form(minimized)   those rows globally minimized: what a `minimized` key holds
//!                   (xark_ir::minimize, as XarkCircuit::for_setup runs it)
//! form  = u64 n ‖ n × (u32 var id ‖ u8 visibility)   every variable, ascending id;
//!                                                    0 public, 1 private, 2 internal
//!         u64 n ‖ n × u32 var id                     public inputs, Groth16 instance
//!                                                    order (ascending id)
//!         u64 n ‖ n × (lc a ‖ lc b ‖ lc c)            rows, in keyed order
//! lc    = fe constant ‖ u32 n ‖ n × (u32 var id ‖ fe coefficient)   terms as stored
//! ```

use std::collections::BTreeMap;
use std::process::Command;
use std::sync::Mutex;

use anyhow::{Context, Result, bail};
use num_bigint::{BigInt, BigUint};
use sha2::{Digest, Sha256};
use xark_ir::{FieldConst, LinearCombination, R1csProgram, Visibility};

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

/// Build the circuit crate at `dir` and digest its keyed rows, after checking the
/// compact artifact expands to exactly the flat lowering.
fn digest(dir: &std::path::Path, target: &std::path::Path) -> Result<String> {
    keyed_digest(&build(dir, target)?)
}

/// The `circuit.xbc` the circuit crate at `dir` builds to, checked against the flat
/// lowering.
fn build(dir: &std::path::Path, target: &std::path::Path) -> Result<Vec<u8>> {
    let wasm = xark_frontend::build_crate(dir, target).map_err(|e| anyhow::anyhow!("{e}"))?;
    let out = xark_frontend::lower_module(&wasm, xark_ir::FieldSpec::named("bn254"), false, false)
        .map_err(|e| anyhow::anyhow!("{e}"))?
        .output;
    xark_ir::function_decode::verify_blob_matches(&out.xbc, &out.r1cs, &out.primitive)
        .map_err(|e| anyhow::anyhow!("circuit.xbc doesn't match the flat lowering: {e}"))?;
    Ok(out.xbc)
}

/// The keyed-rows digest of `xbc` (the module doc has its layout), as 64 hex digits:
/// both forms a key can hold, made by the same calls `xark setup` makes.
pub fn keyed_digest(xbc: &[u8]) -> Result<String> {
    let reduced = xark_ir::function_decode::expand_function_blob_reduced(xbc)
        .map_err(|e| anyhow::anyhow!(e))?
        .into_r1cs();
    let minimized = xark_ir::minimize(&reduced);
    forms_digest(&reduced, &minimized)
}

/// The digest of a circuit whose keys hold `reduced` or `minimized`.
fn forms_digest(reduced: &R1csProgram, minimized: &R1csProgram) -> Result<String> {
    let decimal = reduced
        .field
        .modulus_decimal
        .as_deref()
        .context("the circuit has no field modulus")?;
    let p: BigUint = decimal.parse().context("parsing the field modulus")?;
    let width = (p.bits() as usize).div_ceil(8);
    let p = BigInt::from(p);
    let fe = |h: &mut Sha256, k: &FieldConst| {
        let mut bytes = match k.as_i64() {
            Some(i) if i >= 0 && width > 8 => i.to_le_bytes().to_vec(),
            _ => (((k.big() % &p) + &p) % &p).to_bytes_le().1,
        };
        bytes.resize(width, 0);
        h.update(&bytes);
    };
    let lc = |h: &mut Sha256, lc: &LinearCombination| {
        fe(h, &lc.constant);
        h.update((lc.terms.len() as u32).to_le_bytes());
        for t in &lc.terms {
            h.update(t.var.to_le_bytes());
            fe(h, &t.coeff);
        }
    };
    let mut h = Sha256::new();
    h.update(b"xark keyed rows v1");
    h.update((decimal.len() as u32).to_le_bytes());
    h.update(decimal.as_bytes());
    for prog in [reduced, minimized] {
        let mut vars: Vec<_> = prog.variables.iter().collect();
        vars.sort_by_key(|v| v.id);
        h.update((vars.len() as u64).to_le_bytes());
        for v in &vars {
            h.update(v.id.to_le_bytes());
            h.update([match v.visibility {
                Visibility::Public => 0u8,
                Visibility::Private => 1,
                Visibility::Internal => 2,
            }]);
        }
        let public: Vec<u32> = vars
            .iter()
            .filter(|v| v.visibility == Visibility::Public)
            .map(|v| v.id)
            .collect();
        h.update((public.len() as u64).to_le_bytes());
        for id in public {
            h.update(id.to_le_bytes());
        }
        h.update((prog.constraints.len() as u64).to_le_bytes());
        for row in &prog.constraints {
            for side in [&row.a, &row.b, &row.c] {
                lc(&mut h, side);
            }
        }
    }
    Ok(hex(&h.finalize()))
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
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

#[cfg(test)]
mod tests {
    use super::*;

    /// An optimizer that drops a constraint or merges two (bug checklist 12,
    /// circom#425) must not pass as a change that leaves the circuit alone: with
    /// either minimizer pass mutated to drop one keyed row, or to merge two (a CSE
    /// that keeps one row for two that differ), or with a public input keyed as
    /// private, `digests --check` reports the example.
    #[test]
    fn a_minimizer_that_drops_or_merges_a_keyed_row_fails_the_check() {
        let name = "sha256";
        let xbc = build(
            &crate::root().join("examples").join(name),
            &crate::target_dir().join("digests-test").join(name),
        )
        .unwrap();
        let committed =
            std::fs::read_to_string(crate::root().join("tests/stable-digests.txt")).unwrap();
        let line = |d: &str| format!("{name} {d}");
        let old = committed
            .lines()
            .find_map(|l| l.strip_prefix(&format!("{name} ")))
            .unwrap()
            .to_string();
        let check = |d: &str| diff(&committed, &committed.replace(&line(&old), &line(d)));

        let reduced = xark_ir::function_decode::expand_function_blob_reduced(&xbc)
            .unwrap()
            .into_r1cs();
        let minimized = xark_ir::minimize(&reduced);
        assert!(check(&forms_digest(&reduced, &minimized).unwrap()).is_empty());
        assert!(minimized.constraints.len() > 2, "{name} keys too few rows");

        let mut dropped = reduced.clone();
        dropped.constraints.pop();
        let pass1_drops = forms_digest(&dropped, &xark_ir::minimize(&dropped)).unwrap();
        let mut dropped = minimized.clone();
        dropped.constraints.remove(1);
        let pass2_drops = forms_digest(&reduced, &dropped).unwrap();
        let mut merged = minimized.clone();
        merged.constraints[1] = merged.constraints[0].clone();
        let pass2_merges = forms_digest(&reduced, &merged).unwrap();
        let mut private = minimized.clone();
        let input = private
            .variables
            .iter_mut()
            .find(|v| v.visibility == Visibility::Public)
            .unwrap();
        input.visibility = Visibility::Private;
        let input_private = forms_digest(&reduced, &private).unwrap();

        for got in [pass1_drops, pass2_drops, pass2_merges, input_private] {
            assert_eq!(
                check(&got),
                [format!("- {name} {old}"), format!("+ {name} {got}")]
            );
        }
    }
}
