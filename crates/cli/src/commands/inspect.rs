use std::path::PathBuf;

use anyhow::Result;
use clap::Args;
use serde::Serialize;

use crate::noir_project::NoirProject;

use super::conditional_args::bail_on_missing_args;

use xark_acir_r1cs::artifact::parse_artifact_file;
use xark_acir_r1cs::lower::{estimate_constraints, summarize_opcodes, LoweredAcirCircuit};
use xark_acir_r1cs::opcodes::brillig_check::check_brillig_outputs_pinned;
use xark_acir_r1cs::opcodes::CoverageSummary;

#[derive(Args, Debug)]
pub struct InspectArgs {
    /// Path to a Noir project directory (the one containing Nargo.toml).
    /// Inferred when run from inside a Noir project.
    #[arg(long)]
    pub path: Option<PathBuf>,

    /// Path to a Noir artifact JSON (the file at `target/<name>.json`).
    /// Inferred when run from inside a Noir project.
    #[arg(long)]
    pub artifact: Option<PathBuf>,

    /// Emit machine-readable JSON instead of human-readable text.
    #[arg(long, default_value_t = false)]
    pub json: bool,

    /// Run the Brillig output-pinning `(SI)` invariant check and exit
    /// non-zero if any `BrilligCall` output witness is not referenced by a
    /// surrounding constraining opcode. See `docs/brillig.md` for the
    /// invariant statement and `crates/acir-r1cs/src/opcodes/brillig_check.rs`
    /// for the analyser. Recommended for production-deployment gating.
    #[arg(long, default_value_t = false)]
    pub strict: bool,
}

#[derive(Debug, Serialize)]
struct InspectReport {
    circuit_name: String,
    noir_version: String,
    program_hash: String,
    opcode_count: usize,
    witness_count: usize,
    public_input_count: usize,
    private_witness_count_estimate: usize,
    supported_opcode_count: usize,
    unsupported_opcode_count: usize,
    unsupported_opcodes: Vec<String>,
    estimated_r1cs_constraints: usize,
    circuit_hash: Option<String>,
    helper_function_count: usize,
    helper_function_names: Vec<String>,
}

pub fn run(args: InspectArgs) -> Result<()> {
    let path = match args.path {
        Some(p) => p,
        None => std::env::current_dir()?,
    };
    let project = NoirProject::find_at(&path)?;

    let artifact_path = args
        .artifact
        .or_else(|| project.as_ref().map(|p| p.artifact_path()));

    let Some(artifact_path) = artifact_path else {
        bail_on_missing_args("inspect", &["--artifact <PATH>"]);
    };

    let artifact = parse_artifact_file(&artifact_path)?;
    let opcodes = artifact.opcodes();

    let CoverageSummary {
        total,
        supported,
        unsupported,
        unsupported_kinds,
    } = summarize_opcodes(opcodes);

    let est = estimate_constraints(opcodes);

    let private_count_estimate = artifact
        .witness_count
        .saturating_sub(artifact.public_inputs.len());

    let circuit_hash = if unsupported == 0 {
        // Re-lower so we can compute a stable circuit hash.
        match LoweredAcirCircuit::new(artifact.clone()) {
            Ok(lowered) => Some(lowered.circuit_hash()),
            Err(_) => None,
        }
    } else {
        None
    };

    let helper_function_count = artifact.num_helper_functions();
    let helper_function_names = artifact.helper_function_names();

    let report = InspectReport {
        circuit_name: artifact.circuit_name.clone(),
        noir_version: artifact.metadata.noir_version.clone(),
        program_hash: artifact.metadata.program_hash.clone(),
        opcode_count: total,
        witness_count: artifact.witness_count,
        public_input_count: artifact.public_inputs.len(),
        private_witness_count_estimate: private_count_estimate,
        supported_opcode_count: supported,
        unsupported_opcode_count: unsupported,
        unsupported_opcodes: unsupported_kinds,
        estimated_r1cs_constraints: est,
        circuit_hash,
        helper_function_count,
        helper_function_names,
    };

    if args.json {
        let s = serde_json::to_string_pretty(&report)?;
        println!("{s}");
    } else {
        print_human(&report);
    }

    if args.strict {
        let report = check_brillig_outputs_pinned(opcodes);
        if report.is_ok() {
            eprintln!(
                "Brillig pinning OK: {} output(s) all referenced by surrounding opcodes.",
                report.brillig_outputs_total
            );
        } else {
            eprintln!(
                "Brillig pinning FAILED: {} unpinned output(s) out of {} total — \
                 this is a `(SI)`-invariant violation; see docs/brillig.md.\n\
                 Unpinned witness indices: {:?}",
                report.unpinned_outputs.len(),
                report.brillig_outputs_total,
                report.unpinned_outputs
            );
            anyhow::bail!("Brillig output-pinning check failed under --strict");
        }
    }

    Ok(())
}

fn print_human(r: &InspectReport) {
    println!("Circuit name: {}", r.circuit_name);
    println!("Noir version: {}", r.noir_version);
    println!("Program hash: {}", r.program_hash);
    println!("Opcode count: {}", r.opcode_count);
    println!("Witness count: {}", r.witness_count);
    println!("Public input count: {}", r.public_input_count);
    println!(
        "Private witness count (est): {}",
        r.private_witness_count_estimate
    );
    println!("Supported opcode count: {}", r.supported_opcode_count);
    println!("Unsupported opcode count: {}", r.unsupported_opcode_count);
    if !r.unsupported_opcodes.is_empty() {
        println!("Unsupported opcodes:");
        for u in &r.unsupported_opcodes {
            println!(" - {u}");
        }
    }
    println!(
        "Estimated R1CS constraints: {}",
        r.estimated_r1cs_constraints
    );
    println!("Helper function count: {}", r.helper_function_count);
    if !r.helper_function_names.is_empty() {
        println!("Helper functions:");
        for name in &r.helper_function_names {
            println!(" - {name}");
        }
    }
    if let Some(h) = &r.circuit_hash {
        println!("Circuit hash (xark): {h}");
    }
}
