use std::fs;
use std::path::{Path, PathBuf};

use anyhow::{Context, Result};
use clap::Args;
use rand::rngs::OsRng;
use rand::{CryptoRng, RngCore, SeedableRng};
use rand_chacha::ChaCha20Rng;

use xark_acir_r1cs::artifact::parse_artifact_file;
use xark_acir_r1cs::lower::LoweredAcirCircuit;
use xark_acir_r1cs::public_inputs::extract_public_inputs;
use xark_acir_r1cs::witness::parse_witness_file;

use xark_backend::serialization::{ProofJson, PublicInputsJson};
use xark_backend::{NoirGroth16Circuit, keys::Groth16Keys, proof::ProofBundle, prove};

use super::noir_inferred_args::bail_on_missing_args;
use super::synth_err;
use crate::noir_project::NoirProject;

#[derive(Args, Debug)]
pub struct ProveArgs {
    /// Path to a Noir project directory (the one containing Nargo.toml).
    /// Inferred when run from inside a Noir project.
    #[arg(long, value_hint = clap::ValueHint::DirPath)]
    pub path: Option<PathBuf>,

    /// Path to a Noir artifact JSON (the file at `target/<name>.json`).
    /// Inferred when run from inside a Noir project.
    #[arg(long, value_hint = clap::ValueHint::FilePath)]
    pub artifact: Option<PathBuf>,
    /// Witness file (gzipped). Inferred as `./target/{name}.gz` when run
    /// from inside a Noir project.
    #[arg(long, value_hint = clap::ValueHint::FilePath)]
    pub witness: Option<PathBuf>,
    /// Proving key. Inferred as `./target/groth16/proving_key.bin` when
    /// run from inside a Noir project.
    #[arg(long, value_hint = clap::ValueHint::FilePath)]
    pub proving_key: Option<PathBuf>,
    /// Output path for the proof. Inferred as `./target/groth16/proof.bin`
    /// when run from inside a Noir project.
    #[arg(long, value_hint = clap::ValueHint::FilePath)]
    pub out: Option<PathBuf>,
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
    let path = match args.path {
        Some(p) => p,
        None => std::env::current_dir()?,
    };
    let project = NoirProject::find_at(&path)?;

    let artifact_path = args
        .artifact
        .or_else(|| project.as_ref().map(|p| p.artifact_path()));
    let witness_path = args
        .witness
        .or_else(|| project.as_ref().map(|p| p.witness_path()));
    let pk_path = args
        .proving_key
        .or_else(|| project.as_ref().map(|p| p.proving_key_path()));
    let out_path = args
        .out
        .or_else(|| project.as_ref().map(|p| p.proof_path()));

    let (artifact_path, witness_path, pk_path, out_path) =
        match (artifact_path, witness_path, pk_path, out_path) {
            (Some(a), Some(w), Some(k), Some(o)) => (a, w, k, o),
            (a, w, k, o) => {
                let mut missing = Vec::new();
                if a.is_none() {
                    missing.push("--artifact <PATH>");
                }
                if w.is_none() {
                    missing.push("--witness <PATH>");
                }
                if k.is_none() {
                    missing.push("--proving-key <PATH>");
                }
                if o.is_none() {
                    missing.push("--out <PATH>");
                }
                bail_on_missing_args("prove", &missing);
            }
        };

    let artifact = parse_artifact_file(&artifact_path)
        .with_context(|| format!("parsing artifact {}", artifact_path.display()))?;
    let lowered = LoweredAcirCircuit::new(artifact.clone())?;
    let witness = parse_witness_file(&witness_path)
        .with_context(|| format!("parsing witness {}", witness_path.display()))?;
    let public_inputs = extract_public_inputs(&artifact, &witness)?;

    let pk = Groth16Keys::read_proving_key(&pk_path)
        .with_context(|| format!("reading proving key {}", pk_path.display()))?;

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
    let proof = prove(&pk, circuit, &public_inputs, &mut rng).map_err(synth_err)?;

    let bundle = ProofBundle {
        proof,
        public_inputs: public_inputs.clone(),
    };

    let out_dir = out_path
        .parent()
        .map(|p| p.to_path_buf())
        .unwrap_or_else(|| PathBuf::from("."));
    fs::create_dir_all(&out_dir)
        .with_context(|| format!("creating output dir {}", out_dir.display()))?;

    bundle.write_proof(&out_path)?;
    let proof_json = ProofJson::from_proof(&bundle.proof);
    let proof_json_path = with_extension(&out_path, "json");
    fs::write(&proof_json_path, serde_json::to_string_pretty(&proof_json)?)?;

    let public_path = out_dir.join("public_inputs.json");
    let public_inputs_json = PublicInputsJson::from_fr(&public_inputs);
    fs::write(
        &public_path,
        serde_json::to_string_pretty(&public_inputs_json)?,
    )?;

    println!("Wrote {}", out_path.display());
    println!("Wrote {}", proof_json_path.display());
    println!("Wrote {}", public_path.display());
    Ok(())
}

fn with_extension(path: &Path, ext: &str) -> PathBuf {
    let mut p = path.to_path_buf();
    p.set_extension(ext);
    p
}
