//! `xark check --inputs <JSON|FILE>` — the opt-in, witness-based
//! under-constrained soundness check.
//!
//! Bare `xark check` (no `--inputs`) stays the fast, artifact-free `cargo check`
//! validator in [`crate::cli::cmd_check`]. When `--inputs` is supplied, we opt
//! into the same soundness gate `xark prove` runs, but **without** the expensive
//! `setup` + `prove` steps: build the circuit so `circuit.json` exists, solve
//! the witness from the `--inputs` values, and run
//! [`xark_ir::solver::analyze_underconstrained`]. It reports any derived
//! variable the constraints fail to pin (a value a malicious prover could
//! forge) — no proving keys or proof are produced.

use anyhow::{bail, Result};

use xark_ir::primitive::VarRole;

use super::{
    load_circuit_program, load_profile, parse_inputs_arg, resolve_input_ids, soundness_check,
    CheckArgs,
};
use crate::xark_project::XarkProject;

pub fn run(args: CheckArgs) -> Result<()> {
    // Build the circuit (reuses the `xark build` path) so `circuit.json` exists.
    let mut build_argv = vec![args.crate_dir.clone()];
    if let Some(out) = &args.out {
        build_argv.push("--out".into());
        build_argv.push(out.clone());
    }
    let code = crate::cli::cmd_build(&build_argv);
    if code != 0 {
        bail!("build failed (exit {code}); fix the circuit before `xark check --inputs`");
    }

    // Locate the freshly built `circuit.json` the same way the backend commands
    // do: from `--out` when given, else the crate's default `target/xark/`.
    let base = args.out.clone().unwrap_or_else(|| args.crate_dir.clone());
    let project = XarkProject::resolve(Some(base.into()))?;
    // Expand the self-contained `circuit.xbc` once; the soundness gate solves +
    // checks directly on its R1CS rows (no `to_primitive` flattening).
    let cp = load_circuit_program(&project.circuit_xbc())?;
    let profile = load_profile(&project.xark_dir);

    // Resolve inputs → var ids and run the shared soundness gate (no setup/prove).
    // A best-effort profile lets a bad witness name the failing constraint (and
    // its source line), matching `xark prove` / `xark test`.
    // `check::run` is dispatched only when `--inputs` is present (see `mod::run`).
    let arg = args
        .inputs
        .as_deref()
        .expect("check::run is only reached with --inputs");
    let inputs = parse_inputs_arg(arg)?;
    let id_inputs = resolve_input_ids(&cp.vars, &inputs)?;
    let _assign = soundness_check(&cp, profile.as_ref(), &id_inputs)?;

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
