//! `xark inspect` — print statistics about a built circuit (`circuit.json` +
//! `r1cs.json`): variable counts by visibility, constraint count, and public
//! inputs. The unified analog of master's ACIR `inspect`.

use std::path::PathBuf;

use anyhow::Result;
use clap::Args;

use xark_ir::primitive::VarRole;
use xark_ir::Visibility;

use super::{circuit_hash, load_circuit, load_r1cs};
use crate::xark_project::XarkProject;

#[derive(Args, Debug)]
pub struct InspectArgs {
    /// Circuit crate directory (or its `target/xark/` output dir). Defaults to
    /// the current directory; paths are inferred from `target/xark/`.
    #[arg(value_hint = clap::ValueHint::DirPath)]
    pub path: Option<PathBuf>,

    /// Path to `r1cs.json`. Inferred from `target/xark/` when omitted.
    #[arg(long, value_hint = clap::ValueHint::FilePath)]
    pub r1cs: Option<PathBuf>,
    /// Path to `circuit.json`. Inferred from `target/xark/` when omitted.
    #[arg(long, value_hint = clap::ValueHint::FilePath)]
    pub circuit: Option<PathBuf>,

    /// Emit machine-readable JSON instead of human-readable text.
    #[arg(long, default_value_t = false)]
    pub json: bool,
}

pub fn run(args: InspectArgs) -> Result<()> {
    let project = XarkProject::resolve(args.path.clone())?;
    let r1cs_path = args.r1cs.clone().unwrap_or_else(|| project.r1cs_json());
    let circuit_path = args
        .circuit
        .clone()
        .unwrap_or_else(|| project.circuit_json());

    let r1cs_str = std::fs::read_to_string(&r1cs_path).map_err(|e| {
        anyhow::anyhow!(
            "reading {} (run `xark build` first?): {e}",
            r1cs_path.display()
        )
    })?;
    let prog = load_r1cs(&r1cs_path)?;
    let prim = load_circuit(&circuit_path).ok();

    let mut num_public = 0usize;
    let mut num_private = 0usize;
    let mut num_internal = 0usize;
    for v in &prog.variables {
        match v.visibility {
            Visibility::Public => num_public += 1,
            Visibility::Private => num_private += 1,
            Visibility::Internal => num_internal += 1,
        }
    }
    let public_names: Vec<&str> = prog
        .variables
        .iter()
        .filter(|v| v.visibility == Visibility::Public)
        .map(|v| v.name.as_str())
        .collect();
    let private_names: Vec<&str> = prog
        .variables
        .iter()
        .filter(|v| v.visibility == Visibility::Private)
        .map(|v| v.name.as_str())
        .collect();

    let num_derived = prim
        .as_ref()
        .map(|p| p.vars.iter().filter(|v| v.role == VarRole::Derived).count());
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
            "circuit_hash": circuit_hash(&r1cs_str),
        });
        println!("{}", serde_json::to_string_pretty(&report)?);
    } else {
        println!("Field:                {}", prog.field.name);
        println!("Variables:            {}", prog.variables.len());
        println!("  public inputs:      {num_public} {public_names:?}");
        println!("  private inputs:     {num_private} {private_names:?}");
        println!("  internal:           {num_internal}");
        if let Some(d) = num_derived {
            println!("  derived (witness):  {d}");
        }
        println!("Constraints:          {}", prog.constraints.len());
        if let Some(w) = num_witness_gen {
            println!("Witness-gen ops:      {w}");
        }
        println!("Circuit hash (sha256): {}", circuit_hash(&r1cs_str));
    }
    Ok(())
}
