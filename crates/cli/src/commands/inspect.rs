//! `xark inspect` — print statistics about a built circuit (`circuit.xbc`):
//! variable counts by visibility, constraint count, and public inputs.

use std::path::PathBuf;

use anyhow::Result;
use clap::Args;

use xark_ir::Visibility;
use xark_ir::primitive::VarRole;

use super::{load_backend_r1cs, load_primitive};
use crate::xark_project::XarkProject;

#[derive(Args, Debug)]
pub struct InspectArgs {
    /// Circuit crate directory (or its `target/xark/` output dir). Defaults to
    /// the current directory; paths are inferred from `target/xark/`.
    #[arg(value_hint = clap::ValueHint::DirPath)]
    pub path: Option<PathBuf>,

    /// Emit machine-readable JSON instead of human-readable text.
    #[arg(long, default_value_t = false)]
    pub json: bool,
}

pub fn run(args: InspectArgs) -> Result<()> {
    let project = XarkProject::resolve(args.path.clone())?;
    crate::cli::build_if_needed(&project.xark_dir, false)?;
    let (prog, fingerprint) = load_backend_r1cs(&project.circuit_xbc())?;
    let prim = load_primitive(&project.circuit_xbc()).ok();
    // Two fingerprints: the constraint system's (`xark build` prints it; a key fits
    // every build with it), and this build's file's. Keys record both.
    let digest = std::fs::read(project.circuit_xbc())
        .ok()
        .map(|b| format!("{:032x}", xark_ir::function_decode::stream_digest(&b)));

    let num_internal = prog
        .variables
        .iter()
        .filter(|v| v.visibility == Visibility::Internal)
        .count();
    // Declared inputs come from the primitive program's roles, not the R1CS
    // visibility: the solver *derives* internal witnesses (e.g. `to_bits`
    // range-check bits), which the R1CS still marks `Private`. Listing those as
    // inputs is wrong — the prover never supplies them. Fall back to visibility
    // only when the primitive program is unavailable (older builds).
    let (public_names, private_names): (Vec<&str>, Vec<&str>) = match prim.as_ref() {
        Some(p) => (
            p.vars
                .iter()
                .filter(|v| v.role == VarRole::PublicInput)
                .map(|v| v.name.as_str())
                .collect(),
            p.vars
                .iter()
                .filter(|v| v.role == VarRole::PrivateInput)
                .map(|v| v.name.as_str())
                .collect(),
        ),
        None => (
            prog.variables
                .iter()
                .filter(|v| v.visibility == Visibility::Public)
                .map(|v| v.name.as_str())
                .collect(),
            prog.variables
                .iter()
                .filter(|v| v.visibility == Visibility::Private)
                .map(|v| v.name.as_str())
                .collect(),
        ),
    };
    // Report the declared-input counts (what a user supplies), not the raw R1CS
    // visibility tally that lumps derived witnesses in with private inputs.
    let num_public = public_names.len();
    let num_private = private_names.len();

    // The solver-derived witness nodes (multiplication + hint outputs). Keep
    // their names: seeing them is useful for debugging — e.g. telling two
    // adjacent bit decompositions apart — which a bare count hides.
    let derived_names: Option<Vec<&str>> = prim.as_ref().map(|p| {
        p.vars
            .iter()
            .filter(|v| v.role == VarRole::Derived)
            .map(|v| v.name.as_str())
            .collect()
    });
    let num_derived = derived_names.as_ref().map(|n| n.len());
    let num_witness_gen = prim.as_ref().map(|p| p.witness_gen.len());

    if args.json {
        let report = serde_json::json!({
            "field": prog.field.name,
            "num_variables": prog.variables.len(),
            "num_constraints": prog.constraints.len(),
            "num_public_inputs": num_public,
            "num_private_inputs": num_private,
            "num_internal": num_internal,
            "num_derived": num_derived,
            "num_witness_gen_ops": num_witness_gen,
            "public_inputs": public_names,
            "private_inputs": private_names,
            "derived_witnesses": derived_names,
            "digest": digest,
            "circuit_hash": fingerprint,
        });
        println!("{}", serde_json::to_string_pretty(&report)?);
    } else {
        println!("Field:                {}", prog.field.name);
        println!("Variables:            {}", prog.variables.len());
        // Declared inputs by name and type (from `schema.json`), not leaf by leaf.
        let summary = super::load_schema(&project.xark_dir).map(|s| s.summary());
        let line = |public: bool, n: usize, names: &[&str]| match &summary {
            Some(inputs) => {
                let parts: Vec<String> = inputs
                    .iter()
                    .filter(|i| i.public == public)
                    .map(|i| format!("{}: {}", i.name, i.ty))
                    .collect();
                let leaves = if n == 1 { "leaf" } else { "leaves" };
                match parts.is_empty() {
                    true => "none".to_string(),
                    false => format!("{} ({n} {leaves})", parts.join(", ")),
                }
            }
            None => format!("{n} {names:?}"),
        };
        println!(
            "  public inputs:      {}",
            line(true, num_public, &public_names)
        );
        println!(
            "  private inputs:     {}",
            line(false, num_private, &private_names)
        );
        println!("  internal:           {num_internal}");
        if let Some(names) = &derived_names {
            println!(
                "  derived (witness):  {} {}",
                names.len(),
                format_witness_preview(names)
            );
        }
        println!("Constraints:          {}", prog.constraints.len());
        if let Some(w) = num_witness_gen {
            println!("Witness-gen ops:      {w}");
        }
        if let Some(d) = &digest {
            println!("Circuit digest:       {d}  (the R1CS, as `xark build` prints it)");
        }
        println!("circuit.xbc sha256:   {fingerprint}  (this build's file)");
    }
    Ok(())
}

/// Render the solver-derived witness nodes as `private[<name>]` slots, capped so
/// a circuit with thousands of them doesn't flood the terminal (the full list is
/// in `--json`). Each is a private witness the prover fills — never a declared
/// input — and adjacent ones (e.g. two bit decompositions) stay distinguishable.
fn format_witness_preview(names: &[&str]) -> String {
    const MAX: usize = 24;
    let shown: Vec<String> = names
        .iter()
        .take(MAX)
        .map(|n| format!("private[{n}]"))
        .collect();
    if names.len() > MAX {
        format!("[{}, … (+{} more)]", shown.join(", "), names.len() - MAX)
    } else {
        format!("[{}]", shown.join(", "))
    }
}

#[cfg(test)]
mod tests {
    use super::format_witness_preview;

    #[test]
    fn witnesses_render_as_indexed_private_slots() {
        assert_eq!(
            format_witness_preview(&["w0", "w1", "w2"]),
            "[private[w0], private[w1], private[w2]]"
        );
    }

    #[test]
    fn long_witness_lists_are_capped() {
        let names: Vec<String> = (0..30).map(|i| format!("w{i}")).collect();
        let refs: Vec<&str> = names.iter().map(String::as_str).collect();
        let out = format_witness_preview(&refs);
        assert!(out.starts_with("[private[w0], private[w1],"));
        assert!(out.ends_with("… (+6 more)]")); // 30 - 24 cap
    }
}
