//! `xark verify` — verify a Groth16 proof against its public inputs.
//!
//! Loads the verifying key and proof written by `xark setup` / `xark prove`.
//! Public inputs come from the circuit's public vars + `--input` values when
//! provided; otherwise from the `public_inputs.bin` written by `xark prove`.

use std::path::PathBuf;

use anyhow::{Context, Result};
use ark_bn254::Fr;
use clap::Args;

use xark_backend::serialization::read_public_inputs;
use xark_backend::{keys::Groth16Keys, proof::ProofBundle, verify};

use super::{load_r1cs, parse_inputs, public_inputs_from_inputs};
use crate::xark_project::XarkProject;

#[derive(Args, Debug)]
pub struct VerifyArgs {
    /// Circuit crate directory (or its `target/xark/` output dir). Defaults to
    /// the current directory; paths are inferred from `target/xark/`.
    #[arg(value_hint = clap::ValueHint::DirPath)]
    pub path: Option<PathBuf>,

    /// Circuit public input as `name=value` (repeatable). When omitted, the
    /// public inputs are read from `public_inputs.bin`.
    #[arg(long = "input", value_name = "NAME=VALUE")]
    pub inputs: Vec<String>,

    /// Verifying key. Inferred as `target/xark/vk.bin` when omitted.
    #[arg(long, value_hint = clap::ValueHint::FilePath)]
    pub verifying_key: Option<PathBuf>,
    /// Proof file. Inferred as `target/xark/proof.bin` when omitted.
    #[arg(long, value_hint = clap::ValueHint::FilePath)]
    pub proof: Option<PathBuf>,
    /// Public inputs file. Inferred as `target/xark/public_inputs.bin`.
    #[arg(long, value_hint = clap::ValueHint::FilePath)]
    pub public_inputs: Option<PathBuf>,
    /// Path to `r1cs.json` (used to order `--input` public values). Inferred
    /// from `target/xark/` when omitted.
    #[arg(long, value_hint = clap::ValueHint::FilePath)]
    pub r1cs: Option<PathBuf>,
}

pub fn run(args: VerifyArgs) -> Result<()> {
    let project = XarkProject::resolve(args.path.clone())?;
    let vk_path = args
        .verifying_key
        .clone()
        .unwrap_or_else(|| project.verifying_key());
    let proof_path = args.proof.clone().unwrap_or_else(|| project.proof());

    let vk = Groth16Keys::read_verifying_key(&vk_path).with_context(|| {
        format!(
            "reading verifying key {} (run `xark setup` first?)",
            vk_path.display()
        )
    })?;
    let proof = ProofBundle::read_proof(&proof_path)
        .with_context(|| format!("reading proof {}", proof_path.display()))?;

    // Public inputs: from `--input` values (recomputed) when given, else from
    // the `public_inputs.bin` the prover wrote.
    let public: Vec<Fr> = if args.inputs.is_empty() {
        let path = args
            .public_inputs
            .clone()
            .unwrap_or_else(|| project.public_inputs());
        read_public_inputs(&path).with_context(|| {
            format!(
                "reading {} (pass --input <name=value> or run `xark prove` first)",
                path.display()
            )
        })?
    } else {
        let r1cs_path = args.r1cs.clone().unwrap_or_else(|| project.r1cs_json());
        let prog = load_r1cs(&r1cs_path)?;
        let inputs = parse_inputs(&args.inputs)?;
        public_inputs_from_inputs(&prog, &inputs)?
    };

    let ok = verify(&vk, &proof, &public).map_err(super::synth_err)?;
    println!(
        "{}",
        if ok {
            crate::style::brand("✅ Proof verified")
        } else {
            crate::style::err("❌ Proof verification failed")
        }
    );
    if !ok {
        std::process::exit(2);
    }
    Ok(())
}
