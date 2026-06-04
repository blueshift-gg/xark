use std::fs;
use std::path::PathBuf;

use anyhow::{Context, Result};
use clap::Args;

use groth16_backend::{
    keys::Groth16Keys, proof::ProofBundle, serialization::PublicInputsJson, verify,
};

use super::synth_err;

#[derive(Args, Debug)]
pub struct VerifyArgs {
    #[arg(long)]
    pub verifying_key: PathBuf,
    #[arg(long)]
    pub proof: PathBuf,
    #[arg(long)]
    pub public_inputs: PathBuf,
}

pub fn run(args: VerifyArgs) -> Result<()> {
    let vk = Groth16Keys::read_verifying_key(&args.verifying_key)
        .with_context(|| format!("reading verifying key {}", args.verifying_key.display()))?;
    let proof = ProofBundle::read_proof(&args.proof)
        .with_context(|| format!("reading proof {}", args.proof.display()))?;
    let public_inputs_bytes = fs::read(&args.public_inputs)
        .with_context(|| format!("reading {}", args.public_inputs.display()))?;
    let public_inputs_json: PublicInputsJson = serde_json::from_slice(&public_inputs_bytes)?;
    let public_inputs = public_inputs_json.into_fr()?;

    let ok = verify(&vk, &proof, &public_inputs).map_err(synth_err)?;
    println!("Proof verified: {ok}");
    if !ok {
        std::process::exit(2);
    }
    Ok(())
}
