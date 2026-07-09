//! `xark prove` — produce a Groth16 proof for a built circuit.
//!
//! Self-contained: loads `r1cs.json` + `circuit.json`, *solves* the witness from
//! the `--input name=value` values (via the reference solver), loads the proving
//! key written by `xark setup`, and runs the shared `xark_backend` prover. The
//! proof and its public inputs are written next to the build output.

use std::collections::BTreeMap;
use std::fs;
use std::path::PathBuf;

use anyhow::{Context, Result};
use clap::Args;
use rand::rngs::OsRng;
use rand::{CryptoRng, RngCore, SeedableRng};
use rand_chacha::ChaCha20Rng;

use xark_backend::proof::ProofBundle;
use xark_backend::serialization::{
    proof_to_snarkjs, public_inputs_to_snarkjs, write_public_inputs,
};
use xark_backend::{keys::Groth16Keys, prove};
use xark_ir::VarId;
use xark_prover::{fr_from_decimal, XarkCircuit};

use super::{load_circuit, load_r1cs, parse_inputs, resolve_input_ids, soundness_check, synth_err};
use crate::xark_project::XarkProject;

#[derive(Args, Debug)]
pub struct ProveArgs {
    /// Circuit crate directory (or its `target/xark/` output dir). Defaults to
    /// the current directory; paths are inferred from `target/xark/`.
    #[arg(value_hint = clap::ValueHint::DirPath)]
    pub path: Option<PathBuf>,

    /// Circuit input as `name=value` (repeatable). Provide every public and
    /// private input the circuit declares.
    #[arg(long = "input", value_name = "NAME=VALUE")]
    pub inputs: Vec<String>,

    /// Path to `r1cs.json`. Inferred from `target/xark/` when omitted.
    #[arg(long, value_hint = clap::ValueHint::FilePath)]
    pub r1cs: Option<PathBuf>,
    /// Path to `circuit.json`. Inferred from `target/xark/` when omitted.
    #[arg(long, value_hint = clap::ValueHint::FilePath)]
    pub circuit: Option<PathBuf>,
    /// Proving key. Inferred as `target/xark/pk.bin` when omitted.
    #[arg(long, value_hint = clap::ValueHint::FilePath)]
    pub proving_key: Option<PathBuf>,
    /// Output path for the proof. Inferred as `target/xark/proof.bin`.
    #[arg(long, value_hint = clap::ValueHint::FilePath)]
    pub out: Option<PathBuf>,
    /// Reproducible-randomness escape hatch for test fixtures **only**. Groth16
    /// proof randomness blinds the witness — making it reproducible leaks
    /// information about the witness across proofs.
    #[arg(long, value_name = "SEED")]
    pub deterministic_rng: Option<u64>,
}

/// See `setup::SetupRng` for rationale: `prove` bounds its RNG by
/// `CryptoRng + RngCore`, which trait objects cannot carry.
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
    let project = XarkProject::resolve(args.path.clone())?;
    let r1cs_path = args.r1cs.clone().unwrap_or_else(|| project.r1cs_json());
    let circuit_path = args
        .circuit
        .clone()
        .unwrap_or_else(|| project.circuit_json());
    let pk_path = args
        .proving_key
        .clone()
        .unwrap_or_else(|| project.proving_key());
    let proof_out = args.out.clone().unwrap_or_else(|| project.proof());
    let out_dir = proof_out
        .parent()
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from("."));

    let prog = load_r1cs(&r1cs_path)?;
    let prim = load_circuit(&circuit_path)?;
    let inputs = parse_inputs(&args.inputs)?;

    // Resolve input names → variable ids for the solver (shared with `check`).
    let id_inputs = resolve_input_ids(&prim, &inputs)?;

    // Solve the witness, then run the shared under-constrained soundness gate.
    // This is the *witness-based* check: it needs the solved assignment (hence
    // it runs here, before any key-loading / synthesis), and rejects circuits
    // with a derived variable the constraints fail to pin uniquely. It returns
    // the solved assignment on success.
    let assign_fp = soundness_check(&prim, &id_inputs)?;

    let assign: BTreeMap<VarId, ark_bn254::Fr> = assign_fp
        .iter()
        .map(|(k, v)| (*k, fr_from_decimal(&v.to_decimal())))
        .collect();

    let circuit = XarkCircuit::for_proving(prog, assign);
    // reject a malformed `r1cs.json` before synthesis (clean error, not a panic)
    circuit
        .validate()
        .map_err(|e| anyhow::anyhow!("malformed circuit: {e}"))?;
    let public = circuit.public_inputs();

    let pk = Groth16Keys::read_proving_key(&pk_path).with_context(|| {
        format!(
            "reading proving key {} (run `xark setup` first?)",
            pk_path.display()
        )
    })?;

    // reproducible randomness breaks zero-knowledge on a production key
    if args.deterministic_rng.is_some() && key_is_production_safe(&pk_path) {
        anyhow::bail!(
            "--deterministic-rng cannot be used with a production key \
             (metadata.production_safe = true): reproducible prover randomness breaks \
             zero-knowledge. Remove the flag to prove with OS randomness."
        );
    }

    let mut rng = match args.deterministic_rng {
        Some(seed) => {
            eprintln!(
                "WARN: --deterministic-rng makes proofs reproducible; do not use in production."
            );
            ProveRng::Det(ChaCha20Rng::seed_from_u64(seed))
        }
        None => ProveRng::Os(OsRng),
    };
    let proof = prove(&pk, circuit, &public, &mut rng).map_err(synth_err)?;

    let bundle = ProofBundle {
        proof,
        public_inputs: public.clone(),
    };

    fs::create_dir_all(&out_dir)
        .with_context(|| format!("creating output dir {}", out_dir.display()))?;
    bundle.write_proof(&proof_out)?;

    // Public inputs as canonical binary (primary format for verify/export).
    let public_path = out_dir.join("public_inputs.bin");
    write_public_inputs(&public, &public_path)?;

    // snarkjs-compatible proof.
    let snarkjs_proof_path = out_dir.join("snarkjs-proof.json");
    let snarkjs_proof = proof_to_snarkjs(&bundle.proof);
    fs::write(
        &snarkjs_proof_path,
        serde_json::to_string_pretty(&snarkjs_proof)?,
    )?;

    // snarkjs-compatible public inputs.
    let snarkjs_public_path = out_dir.join("snarkjs-public.json");
    let snarkjs_public = public_inputs_to_snarkjs(&public);
    fs::write(
        &snarkjs_public_path,
        serde_json::to_string_pretty(&snarkjs_public)?,
    )?;

    println!("Wrote {}", proof_out.display());
    println!("Wrote {}", snarkjs_proof_path.display());
    println!("Wrote {}", snarkjs_public_path.display());
    println!("Wrote {}", public_path.display());
    println!(
        "{}",
        crate::style::brand(&format!(
            "✅ Proof produced and self-checked ({} public input(s)).",
            public.len()
        ))
    );
    Ok(())
}

/// Whether the `metadata.json` beside a proving key marks it production-safe.
fn key_is_production_safe(pk_path: &std::path::Path) -> bool {
    let Some(dir) = pk_path.parent() else {
        return false;
    };
    fs::read_to_string(dir.join("metadata.json"))
        .ok()
        .and_then(|s| serde_json::from_str::<serde_json::Value>(&s).ok())
        .and_then(|v| v.get("production_safe").and_then(|b| b.as_bool()))
        .unwrap_or(false)
}
