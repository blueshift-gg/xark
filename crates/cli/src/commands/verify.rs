use std::fs;
use std::path::PathBuf;

use anyhow::{Context, Result};
use clap::Args;

use xark_backend::{
    keys::Groth16Keys, proof::ProofBundle, serialization::PublicInputsJson, verify,
};

use super::conditional_args::bail_on_missing_args;
use super::synth_err;

use crate::noir_project::NoirProject;

#[derive(Args, Debug)]
pub struct VerifyArgs {
    /// Path to a Noir project directory (the one containing Nargo.toml).
    /// Inferred when run from inside a Noir project.
    #[arg(long)]
    pub path: Option<PathBuf>,

    /// Verifying key. Inferred as `./target/groth16/verifying_key.bin` when
    /// run from inside a Noir project.
    #[arg(long)]
    pub verifying_key: Option<PathBuf>,
    /// Proof file. Inferred as `./target/groth16/proof.bin` when run from
    /// inside a Noir project.
    #[arg(long)]
    pub proof: Option<PathBuf>,
    /// Public inputs JSON. Inferred as `./target/groth16/public_inputs.json`
    /// when run from inside a Noir project.
    #[arg(long)]
    pub public_inputs: Option<PathBuf>,
}

pub fn run(args: VerifyArgs) -> Result<()> {
    let path = match args.path {
        Some(p) => p,
        None => std::env::current_dir()?,
    };
    let project = NoirProject::find_at(&path)?;

    let vk_path = args
        .verifying_key
        .or_else(|| project.as_ref().map(|p| p.verifying_key_path()));
    let proof_path = args
        .proof
        .or_else(|| project.as_ref().map(|p| p.proof_path()));
    let public_inputs_path = args
        .public_inputs
        .or_else(|| project.as_ref().map(|p| p.public_inputs_path()));

    let (vk_path, proof_path, public_inputs_path) = match (vk_path, proof_path, public_inputs_path)
    {
        (Some(v), Some(p), Some(i)) => (v, p, i),
        (v, p, i) => {
            let mut missing = Vec::new();
            if v.is_none() {
                missing.push("--verifying-key <PATH>");
            }
            if p.is_none() {
                missing.push("--proof <PATH>");
            }
            if i.is_none() {
                missing.push("--public-inputs <PATH>");
            }
            bail_on_missing_args("verify", &missing);
        }
    };

    let vk = Groth16Keys::read_verifying_key(&vk_path)
        .with_context(|| format!("reading verifying key {}", vk_path.display()))?;
    let proof = ProofBundle::read_proof(&proof_path)
        .with_context(|| format!("reading proof {}", proof_path.display()))?;
    let public_inputs_bytes = fs::read(&public_inputs_path)
        .with_context(|| format!("reading {}", public_inputs_path.display()))?;
    let public_inputs_json: PublicInputsJson = serde_json::from_slice(&public_inputs_bytes)?;
    let public_inputs = public_inputs_json.into_fr()?;

    let ok = verify(&vk, &proof, &public_inputs).map_err(synth_err)?;
    println!("Proof verified: {ok}");
    if !ok {
        std::process::exit(2);
    }
    Ok(())
}
