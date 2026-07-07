//! `xark setup` — generate Groth16 proving/verifying keys for a circuit.
//!
//! Reads the `r1cs.json` produced by `xark build` and runs either the insecure
//! dev-mode setup (`--insecure-dev-mode`) or the production phase-2 setup from a
//! Powers-of-Tau transcript (`--ptau-file`, or one auto-detected under
//! `target/xark/`). Keys land next to the build output as `pk.bin` / `vk.bin`.

use std::fs;
use std::path::PathBuf;

use anyhow::{bail, Context, Result};
use clap::Args;
use rand::rngs::OsRng;
use rand::{CryptoRng, RngCore, SeedableRng};
use rand_chacha::ChaCha20Rng;

use xark_backend::serialization::VerifyingKeyJson;
use xark_backend::{keys::KeyMetadata, setup};
use xark_prover::XarkCircuit;

use super::{circuit_hash, load_r1cs, num_public_inputs, synth_err};
use crate::xark_project::XarkProject;

#[derive(Args, Debug)]
pub struct SetupArgs {
    /// Circuit crate directory (or its `target/xark/` output dir). Defaults to
    /// the current directory; paths are inferred from `target/xark/`.
    #[arg(value_hint = clap::ValueHint::DirPath)]
    pub path: Option<PathBuf>,

    /// Path to `r1cs.json`. Inferred from `target/xark/` when omitted.
    #[arg(long, value_hint = clap::ValueHint::FilePath)]
    pub r1cs: Option<PathBuf>,
    /// Output directory for keys and metadata. Inferred as `target/xark/`.
    #[arg(long, value_hint = clap::ValueHint::DirPath)]
    pub out: Option<PathBuf>,
    /// Required to run Groth16 setup with locally generated randomness.
    /// By default, the OS RNG drives the trapdoor sampling — still unsuitable
    /// for production (no ceremony, no transcript). **Do not use the resulting
    /// parameters in production.**
    #[arg(long, default_value_t = false)]
    pub insecure_dev_mode: bool,
    /// Reproducible-randomness escape hatch for test fixtures **only**.
    /// Requires `--insecure-dev-mode`. Drives setup with
    /// `ChaCha20Rng::seed_from_u64(<seed>)` so two runs with the same seed
    /// produce byte-identical keys. This trivially leaks the Groth16 trapdoor
    /// and must never be used beyond regenerating committed test fixtures.
    #[arg(long, value_name = "SEED")]
    pub deterministic_rng: Option<u64>,
    /// Production phase-2 setup from a Powers-of-Tau (`.ptau`) transcript.
    /// Mutually exclusive with `--insecure-dev-mode`. When neither is supplied,
    /// `setup` auto-detects a `.ptau` under `target/xark/`, `target/xark/ptau/`,
    /// the crate root, or `<root>/ptau/`.
    #[arg(long, value_name = "PATH", value_hint = clap::ValueHint::FilePath)]
    pub ptau_file: Option<PathBuf>,
    /// 32-byte randomness seed (hex) for the phase-2 `(γ, δ)` derivation.
    /// Optional — auto-generated via OS RNG when not supplied.
    #[arg(long, value_name = "HEX")]
    pub phase2_seed: Option<String>,
}

/// Wrapper RNG threading `CryptoRng + RngCore` through both the OS RNG path and
/// the deterministic test-fixture path. `setup` requires `CryptoRng` (a marker
/// trait) which trait objects can't carry, so an explicit enum is simplest.
#[allow(clippy::large_enum_variant)]
enum SetupRng {
    Det(ChaCha20Rng),
    Os(OsRng),
}

impl RngCore for SetupRng {
    fn next_u32(&mut self) -> u32 {
        match self {
            SetupRng::Det(r) => r.next_u32(),
            SetupRng::Os(r) => r.next_u32(),
        }
    }
    fn next_u64(&mut self) -> u64 {
        match self {
            SetupRng::Det(r) => r.next_u64(),
            SetupRng::Os(r) => r.next_u64(),
        }
    }
    fn fill_bytes(&mut self, dest: &mut [u8]) {
        match self {
            SetupRng::Det(r) => r.fill_bytes(dest),
            SetupRng::Os(r) => r.fill_bytes(dest),
        }
    }
    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), rand::Error> {
        match self {
            SetupRng::Det(r) => r.try_fill_bytes(dest),
            SetupRng::Os(r) => r.try_fill_bytes(dest),
        }
    }
}

impl CryptoRng for SetupRng {}

pub fn run(args: SetupArgs) -> Result<()> {
    let project = XarkProject::resolve(args.path.clone())?;
    let r1cs_path = args.r1cs.clone().unwrap_or_else(|| project.r1cs_json());
    let out_dir = args.out.clone().unwrap_or_else(|| project.xark_dir.clone());

    let r1cs_str = fs::read_to_string(&r1cs_path)
        .with_context(|| format!("reading {} (run `xark build` first?)", r1cs_path.display()))?;
    let prog = load_r1cs(&r1cs_path)?;
    let hash = circuit_hash(&r1cs_str);
    let num_pi = num_public_inputs(&prog);
    let num_constraints = prog.constraints.len();

    // Resolve the ptau path: explicit flag, or auto-detected when neither
    // --ptau-file nor --insecure-dev-mode is supplied.
    let ptau_path: Option<PathBuf> = if args.ptau_file.is_some() {
        args.ptau_file.clone()
    } else if !args.insecure_dev_mode {
        project.find_ptau()
    } else {
        None
    };

    if ptau_path.is_some() && args.insecure_dev_mode {
        bail!(
            "--ptau-file (or auto-detected .ptau) and --insecure-dev-mode are mutually exclusive"
        );
    }
    if ptau_path.is_none() && !args.insecure_dev_mode {
        bail!(
            "Groth16 setup requires trusted randomness.\n\n\
             For production: pass --ptau-file <path> (or place a .ptau under target/xark/).\n\
             For local testing: pass --insecure-dev-mode.\n\
             Do not use insecure dev parameters in production."
        );
    }

    fs::create_dir_all(&out_dir)
        .with_context(|| format!("creating output dir {}", out_dir.display()))?;
    let pk_path = out_dir.join("pk.bin");
    let vk_path = out_dir.join("vk.bin");
    let meta_path = out_dir.join("metadata.json");
    let snarkjs_vk_path = out_dir.join("snarkjs-verification_key.json");

    // --- Production phase-2 path -----------------------------------------
    if let Some(ref ptau_file) = ptau_path {
        let phase2_seed_hex = match &args.phase2_seed {
            Some(s) => s.clone(),
            None => {
                let mut bytes = [0u8; 32];
                OsRng.fill_bytes(&mut bytes);
                hex::encode(bytes)
            }
        };
        let seed_bytes = hex::decode(phase2_seed_hex.trim_start_matches("0x"))
            .context("decoding --phase2-seed as hex")?;
        if seed_bytes.len() != 32 {
            bail!(
                "--phase2-seed must be exactly 32 bytes (got {} bytes)",
                seed_bytes.len()
            );
        }
        let mut seed_arr = [0u8; 32];
        seed_arr.copy_from_slice(&seed_bytes);

        let ptau_bytes =
            fs::read(ptau_file).with_context(|| format!("reading {}", ptau_file.display()))?;
        let ptau = xark_backend::ptau::parse_ptau(&ptau_bytes).context("parsing .ptau file")?;

        let circuit = XarkCircuit::for_setup(prog.clone());
        let keys = xark_backend::ptau::setup_from_ptau(circuit, &ptau, &seed_arr)
            .map_err(|e| anyhow::anyhow!("phase-2 setup failed: {e}"))?;

        keys.write_proving_key(&pk_path)?;
        keys.write_verifying_key(&vk_path)?;

        let mut metadata = KeyMetadata::new_dev(hash, num_pi, num_constraints);
        metadata.setup_mode = "phase2-from-ptau".into();
        metadata.production_safe = true;
        metadata.ptau_source = ptau_file
            .file_name()
            .and_then(|s| s.to_str())
            .map(|s| s.to_string());
        fs::write(&meta_path, serde_json::to_string_pretty(&metadata)?)
            .with_context(|| format!("writing {}", meta_path.display()))?;

        let snarkjs_vk = VerifyingKeyJson::from_vk(&keys.verifying_key);
        fs::write(&snarkjs_vk_path, serde_json::to_string_pretty(&snarkjs_vk)?)?;

        println!("Wrote {}", pk_path.display());
        println!("Wrote {}", vk_path.display());
        println!("Wrote {}", snarkjs_vk_path.display());
        println!("Wrote {}", meta_path.display());
        println!(
            "\nphase2-from-ptau setup complete. Production safety depends on the \
             .ptau ceremony you used."
        );
        return Ok(());
    }

    // --- Dev-mode path ---------------------------------------------------
    let circuit = XarkCircuit::for_setup(prog.clone());
    let mut rng = match args.deterministic_rng {
        Some(seed) => {
            eprintln!(
                "WARN: --deterministic-rng makes the Groth16 trapdoor recoverable from the \
                 seed; do not reuse the resulting keys outside test fixtures."
            );
            SetupRng::Det(ChaCha20Rng::seed_from_u64(seed))
        }
        None => SetupRng::Os(OsRng),
    };
    let keys = setup(circuit, &mut rng).map_err(synth_err)?;

    keys.write_proving_key(&pk_path)?;
    keys.write_verifying_key(&vk_path)?;

    let snarkjs_vk = VerifyingKeyJson::from_vk(&keys.verifying_key);
    fs::write(&snarkjs_vk_path, serde_json::to_string_pretty(&snarkjs_vk)?)?;

    let mut metadata = KeyMetadata::new_dev(hash, num_pi, num_constraints);
    metadata.deterministic_rng_seed = args.deterministic_rng;
    fs::write(&meta_path, serde_json::to_string_pretty(&metadata)?)
        .with_context(|| format!("writing {}", meta_path.display()))?;

    println!("Wrote {}", pk_path.display());
    println!("Wrote {}", vk_path.display());
    println!("Wrote {}", snarkjs_vk_path.display());
    println!("Wrote {}", meta_path.display());
    println!("\nWARNING: setup_mode = insecure-dev-mode. Do not use in production.");
    Ok(())
}
