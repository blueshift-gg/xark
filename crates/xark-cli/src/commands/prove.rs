use std::fs;
use std::path::{Path, PathBuf};

use anyhow::{Context, Result};
use clap::Args;
use rand::rngs::OsRng;
use rand::{CryptoRng, RngCore, SeedableRng};
use rand_chacha::ChaCha20Rng;

use acir_r1cs::artifact::parse_artifact_file;
use acir_r1cs::lower::LoweredAcirCircuit;
use acir_r1cs::public_inputs::extract_public_inputs;
use acir_r1cs::witness::parse_witness_file;

use groth16_backend::serialization::{ProofJson, PublicInputsJson};
use groth16_backend::{keys::Groth16Keys, proof::ProofBundle, prove, NoirGroth16Circuit};

use super::synth_err;

#[derive(Args, Debug)]
pub struct ProveArgs {
    #[arg(long)]
    pub artifact: PathBuf,
    #[arg(long)]
    pub witness: PathBuf,
    #[arg(long)]
    pub proving_key: PathBuf,
    #[arg(long)]
    pub out: PathBuf,
    /// Reproducible-randomness escape hatch for test fixtures **only**.
    /// When set, drives the Groth16 prover blinders with
    /// `ChaCha20Rng::seed_from_u64(<seed>)` instead of the OS RNG, so two
    /// invocations against the same witness produce byte-identical proofs.
    /// Groth16 proof randomness blinds the witness — making it reproducible
    /// leaks information about the witness across proofs. Default (OS RNG)
    /// gives a fresh, witness-blinding proof per invocation.
    #[arg(long, value_name = "SEED")]
    pub deterministic_rng: Option<u64>,
}

/// See `setup::SetupRng` for rationale: we need an enum because `setup`
/// and `prove` both bound their RNG by `CryptoRng + RngCore`, and trait
/// objects cannot carry the `CryptoRng` marker.
#[allow(clippy::large_enum_variant)]
enum ProveRng {
    Det(ChaCha20Rng),
    Os(OsRng),
}

impl RngCore for ProveRng {
    fn next_u32(&mut self) -> u32 {
        match self {
            ProveRng::Det(r) => r.next_u32(),
            ProveRng::Os(r) => r.next_u32(),
        }
    }

    fn next_u64(&mut self) -> u64 {
        match self {
            ProveRng::Det(r) => r.next_u64(),
            ProveRng::Os(r) => r.next_u64(),
        }
    }

    fn fill_bytes(&mut self, dest: &mut [u8]) {
        match self {
            ProveRng::Det(r) => r.fill_bytes(dest),
            ProveRng::Os(r) => r.fill_bytes(dest),
        }
    }

    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), rand::Error> {
        match self {
            ProveRng::Det(r) => r.try_fill_bytes(dest),
            ProveRng::Os(r) => r.try_fill_bytes(dest),
        }
    }
}

impl CryptoRng for ProveRng {}

pub fn run(args: ProveArgs) -> Result<()> {
    let artifact = parse_artifact_file(&args.artifact)
        .with_context(|| format!("parsing artifact {}", args.artifact.display()))?;
    let lowered = LoweredAcirCircuit::new(artifact.clone())?;
    let witness = parse_witness_file(&args.witness)
        .with_context(|| format!("parsing witness {}", args.witness.display()))?;
    let public_inputs = extract_public_inputs(&artifact, &witness)?;

    let pk = Groth16Keys::read_proving_key(&args.proving_key)
        .with_context(|| format!("reading proving key {}", args.proving_key.display()))?;

    let circuit = NoirGroth16Circuit::for_proving(lowered, witness);

    let mut rng = match args.deterministic_rng {
        Some(seed) => {
            eprintln!(
                "WARN: --deterministic-rng makes proofs reproducible; do not use \
                 in production."
            );
            ProveRng::Det(ChaCha20Rng::seed_from_u64(seed))
        }
        None => ProveRng::Os(OsRng),
    };
    let proof = prove(&pk, circuit, &mut rng).map_err(synth_err)?;

    let bundle = ProofBundle {
        proof,
        public_inputs: public_inputs.clone(),
    };

    let out_dir = args
        .out
        .parent()
        .map(|p| p.to_path_buf())
        .unwrap_or_else(|| PathBuf::from("."));
    fs::create_dir_all(&out_dir)
        .with_context(|| format!("creating output dir {}", out_dir.display()))?;

    bundle.write_proof(&args.out)?;
    let proof_json = ProofJson::from_proof(&bundle.proof);
    let proof_json_path = with_extension(&args.out, "json");
    fs::write(&proof_json_path, serde_json::to_string_pretty(&proof_json)?)?;

    let public_path = out_dir.join("public_inputs.json");
    let public_inputs_json = PublicInputsJson::from_fr(&public_inputs);
    fs::write(
        &public_path,
        serde_json::to_string_pretty(&public_inputs_json)?,
    )?;

    println!("Wrote {}", args.out.display());
    println!("Wrote {}", proof_json_path.display());
    println!("Wrote {}", public_path.display());
    Ok(())
}

fn with_extension(path: &Path, ext: &str) -> PathBuf {
    let mut p = path.to_path_buf();
    p.set_extension(ext);
    p
}
