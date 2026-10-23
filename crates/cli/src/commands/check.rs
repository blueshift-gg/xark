//! `xark check --inputs <JSON|FILE>` — the opt-in, witness-based
//! under-constrained soundness check.
//!
//! Bare `xark check` (no `--inputs`) stays the fast, artifact-free `cargo check`
//! validator in [`crate::cli::cmd_check`]. When `--inputs` is supplied, we opt
//! into the same soundness gate `xark prove` runs, but **without** the expensive
//! `setup` + `prove` steps: build the circuit, solve
//! the witness from the `--inputs` values, and run
//! [`xark_ir::solver::analyze_underconstrained`]. It reports any derived
//! variable the constraints fail to pin (a value a malicious prover could
//! forge) — no proving keys or proof are produced.

use anyhow::{Result, bail};

use xark_ir::primitive::VarRole;

use super::{CheckArgs, load_circuit_program, load_sources, resolve_input_ids, soundness_check};
use crate::xark_project::XarkProject;

pub fn run(args: CheckArgs) -> Result<()> {
    // The circuit, through the `xark build` path.
    let mut build_argv = vec![args.crate_dir.clone()];
    if let Some(out) = &args.out {
        build_argv.push("--out".into());
        build_argv.push(out.clone());
    }
    // Locate `circuit.xbc` the same way the backend commands do: from `--out` when
    // given, else the crate's default `target/xark/`. Build it unless it's current.
    let base = args.out.clone().unwrap_or_else(|| args.crate_dir.clone());
    let current = XarkProject::resolve(Some(base.clone().into())).is_ok_and(|p| {
        crate::cli::stale_build(&p.xark_dir, "circuit.xbc", Some("bn254")).is_none()
    });
    if !current {
        let code = crate::cli::cmd_build(&build_argv);
        if code != 0 {
            bail!("build failed (exit {code}); fix the circuit before `xark check --inputs`");
        }
    }
    let project = XarkProject::resolve(Some(base.into()))?;
    // Expand the self-contained `circuit.xbc` once; the soundness gate solves +
    // checks directly on its R1CS rows (no `to_primitive` flattening).
    let cp = load_circuit_program(&project.circuit_xbc())?;
    let sources = load_sources(&project.xark_dir);

    // Resolve inputs → var ids and run the shared soundness gate (no setup/prove).
    // `sources.json` (best-effort) lets a bad witness name the failing constraint (and
    // its source line), matching `xark prove` / `xark test`.
    let arg = args
        .inputs
        .as_deref()
        .expect("check::run is only reached with --inputs");
    let inputs = super::read_inputs(&project.xark_dir, arg)?;
    let id_inputs = resolve_input_ids(&cp.vars, &inputs)?;
    let _assign = soundness_check(&cp, sources.as_ref(), &id_inputs)?;

    let derived = cp
        .vars
        .iter()
        .filter(|v| matches!(v.role, VarRole::Derived))
        .count();
    println!(
        "{}",
        crate::style::brand(&format!(
            "✅ circuit sound: no under-constrained variables ({derived} derived vars checked)"
        ))
    );
    Ok(())
}
