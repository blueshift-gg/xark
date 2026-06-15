use std::fs;
use std::path::PathBuf;

use anyhow::{Context, Result, bail};
use clap::Args;
use rand::rngs::OsRng;
use rand::{CryptoRng, RngCore, SeedableRng};
use rand_chacha::ChaCha20Rng;

use xark_acir_r1cs::artifact::parse_artifact_file;
use xark_acir_r1cs::lower::LoweredAcirCircuit;

use xark_backend::{NoirGroth16Circuit, keys::KeyMetadata, setup};

use super::noir_inferred_args::bail_on_missing_args;
use super::synth_err;
use crate::noir_project::NoirProject;

#[derive(Args, Debug)]
pub struct SetupArgs {
    /// Path to a Noir project directory (the one containing Nargo.toml).
    /// Inferred when run from inside a Noir project.
    #[arg(long, value_hint = clap::ValueHint::DirPath)]
    pub path: Option<PathBuf>,

    /// Path to a Noir artifact JSON (the file at `target/<name>.json`).
    /// Inferred when run from inside a Noir project.
    #[arg(long, value_hint = clap::ValueHint::FilePath)]
    pub artifact: Option<PathBuf>,
    /// Output directory for proving/verifying keys and metadata.
    /// Inferred as `./target/groth16` when run from inside a Noir project.
    #[arg(long, value_hint = clap::ValueHint::DirPath)]
    pub out: Option<PathBuf>,
    /// Required to run Groth16 setup with locally generated randomness.
    /// By default, the OS RNG (`/dev/urandom` on Unix, BCryptGenRandom on
    /// Windows) drives the trapdoor sampling — the resulting parameters
    /// are still unsuitable for production (no ceremony, no transcript)
    /// but the trapdoor τ is not knowable to anyone reading the binary.
    /// **Do not use the resulting parameters in production.**
    #[arg(long, default_value_t = false)]
    pub insecure_dev_mode: bool,
    /// Reproducible-randomness escape hatch for test fixtures **only**.
    /// Requires `--insecure-dev-mode`. When set, drives setup with
    /// `ChaCha20Rng::seed_from_u64(<seed>)` instead of the OS RNG, so two
    /// runs of `xark setup` with the same seed produce byte-identical
    /// proving/verifying keys. This trivially leaks the Groth16 trapdoor
    /// (anyone with the seed can forge proofs) and must never be used
    /// for anything beyond regenerating committed test fixtures.
    #[arg(long, value_name = "SEED")]
    pub deterministic_rng: Option<u64>,
    /// Production phase-2 setup from a Powers-of-Tau (.ptau) transcript.
    /// When set, runs the deterministic phase-2 contribution against the
    /// supplied transcript and `--phase2-seed`, producing keys that are
    /// usable in production iff the `.ptau` came from an audited ceremony.
    /// Mutually exclusive with `--insecure-dev-mode`.
    ///
    /// When neither `--ptau-file` nor `--insecure-dev-mode` is supplied,
    /// `setup` auto-detects a `.ptau` file from `<project>/ptau/`,
    /// `<project>/ceremony/`, or the project root.
    #[arg(long, value_name = "PATH", value_hint = clap::ValueHint::FilePath)]
    pub ptau_file: Option<PathBuf>,
    /// 32-byte randomness seed (as hex) for the phase-2 `(γ, δ)` derivation.
    /// Optional — auto-generated via OS RNG when not supplied. Pass this to
    /// reproduce byte-identical keys from the same circuit + `.ptau`.
    #[arg(long, value_name = "HEX")]
    pub phase2_seed: Option<String>,
}

/// Wrapper RNG that threads `CryptoRng + RngCore` through both the
/// production-style OS RNG path and the deterministic test-fixture path.
///
/// `Box<dyn RngCore>` would suffice for the `RngCore` bound on `setup`,
/// but `setup` also requires `CryptoRng` (a marker trait) which trait
/// objects can't carry through. An explicit enum is the simplest path.
//
// The `large_enum_variant` lint fires because `ChaCha20Rng` carries a
// ~312 byte state and `OsRng` is zero-sized. We construct exactly one of
// these per `setup` invocation and never move it after the `mut rng =...`
// binding, so paying for an extra `Box` (and a heap allocation) is worse
// than the wasted stack space here.
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

// Both `ChaCha20Rng` and `OsRng` are `CryptoRng`, so the enum is too.
impl CryptoRng for SetupRng {}

pub fn run(args: SetupArgs) -> Result<()> {
    let path = match args.path {
        Some(p) => p,
        None => std::env::current_dir()?,
    };
    let project = NoirProject::find_at(&path)?;

    let artifact_path = args
        .artifact
        .or_else(|| project.as_ref().map(|p| p.artifact_path()));
    let out_dir = args
        .out
        .or_else(|| project.as_ref().map(|p| p.groth16_dir()));

    let (artifact_path, out_dir) = match (artifact_path, out_dir) {
        (Some(a), Some(o)) => (a, o),
        (a, o) => {
            let mut missing = Vec::new();
            if a.is_none() {
                missing.push("--artifact <PATH>");
            }
            if o.is_none() {
                missing.push("--out <DIR>");
            }
            bail_on_missing_args("setup", &missing);
        }
    };

    // --- Resolve the ptau path: explicit flag, or auto-detected from the
    //     Noir project when neither --ptau-file nor --insecure-dev-mode
    //     is supplied.
    let ptau_path: Option<PathBuf> = if args.ptau_file.is_some() {
        args.ptau_file.clone()
    } else if !args.insecure_dev_mode {
        project.as_ref().and_then(|p| p.find_ptau())
    } else {
        None
    };

    // Mutual exclusion: --ptau-file and --insecure-dev-mode are different
    // setup pathways with different trust assumptions.
    if ptau_path.is_some() && args.insecure_dev_mode {
        bail!(
            "--ptau-file (or auto-detected .ptau) and --insecure-dev-mode are mutually exclusive"
        );
    }
    if ptau_path.is_none() && !args.insecure_dev_mode {
        bail!(
            "Groth16 setup requires trusted randomness.\n\n\
 For production: pass --ptau-file <path>.\n\
 For local testing: pass --insecure-dev-mode.\n\
 Do not use insecure dev parameters in production."
        );
    }

    let artifact = parse_artifact_file(&artifact_path)
        .with_context(|| format!("parsing artifact {}", artifact_path.display()))?;
    let lowered = LoweredAcirCircuit::new(artifact.clone())?;

    fs::create_dir_all(&out_dir)
        .with_context(|| format!("creating output dir {}", out_dir.display()))?;

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
            .with_context(|| "decoding --phase2-seed as hex")?;
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
        let ptau =
            xark_backend::ptau::parse_ptau(&ptau_bytes).with_context(|| "parsing.ptau file")?;

        let circuit = NoirGroth16Circuit::for_setup(lowered.clone());
        let keys = xark_backend::ptau::setup_from_ptau(circuit, &ptau, &seed_arr)
            .map_err(|e| anyhow::anyhow!("phase-2 setup failed: {e}"))?;

        let pk_path = out_dir.join("proving_key.bin");
        let vk_path = out_dir.join("verifying_key.bin");
        let meta_path = out_dir.join("metadata.json");

        keys.write_proving_key(&pk_path)?;
        keys.write_verifying_key(&vk_path)?;

        // Re-synthesize for constraint count.
        let cs = ark_relations::gr1cs::ConstraintSystem::<ark_bn254::Fr>::new_ref();
        cs.set_mode(ark_relations::gr1cs::SynthesisMode::Setup);
        let circuit = NoirGroth16Circuit::for_setup(lowered.clone());
        <NoirGroth16Circuit as ark_relations::gr1cs::ConstraintSynthesizer<ark_bn254::Fr>>::generate_constraints(
 circuit,
 cs.clone(),
 )
.map_err(synth_err)?;
        cs.finalize();
        let num_constraints = cs.num_constraints();

        let mut metadata = KeyMetadata::new_dev(
            lowered.circuit_hash(),
            artifact.metadata.noir_version.clone(),
            lowered.num_public_inputs(),
            num_constraints,
        );
        metadata.setup_mode = "phase2-from-ptau".into();
        metadata.production_safe = true;
        fs::write(&meta_path, serde_json::to_string_pretty(&metadata)?)
            .with_context(|| format!("writing {}", meta_path.display()))?;

        println!("Wrote {}", pk_path.display());
        println!("Wrote {}", vk_path.display());
        println!("Wrote {}", meta_path.display());
        println!(
            "\nphase2-from-ptau setup complete. Production safety depends on \
 the.ptau ceremony you used."
        );
        return Ok(());
    }

    // --- Dev-mode path ---------------------------------------------------
    let circuit = NoirGroth16Circuit::for_setup(lowered.clone());

    let mut rng = match args.deterministic_rng {
        Some(seed) => {
            eprintln!(
                "WARN: --deterministic-rng makes the Groth16 trapdoor recoverable \
 from the seed; do not reuse the resulting keys outside test \
 fixtures."
            );
            SetupRng::Det(ChaCha20Rng::seed_from_u64(seed))
        }
        None => SetupRng::Os(OsRng),
    };
    let keys = setup(circuit, &mut rng).map_err(synth_err)?;

    let pk_path = out_dir.join("proving_key.bin");
    let vk_path = out_dir.join("verifying_key.bin");
    let meta_path = out_dir.join("metadata.json");

    keys.write_proving_key(&pk_path)?;
    keys.write_verifying_key(&vk_path)?;

    // Re-synthesize once more (in Setup mode, so the value closures are not
    // invoked) to capture the exact constraint count for metadata.
    let cs = ark_relations::gr1cs::ConstraintSystem::<ark_bn254::Fr>::new_ref();
    cs.set_mode(ark_relations::gr1cs::SynthesisMode::Setup);
    let circuit = NoirGroth16Circuit::for_setup(lowered.clone());
    <NoirGroth16Circuit as ark_relations::gr1cs::ConstraintSynthesizer<ark_bn254::Fr>>::generate_constraints(
 circuit,
 cs.clone(),
 )
.map_err(synth_err)?;
    cs.finalize();
    let num_constraints = cs.num_constraints();

    let mut metadata = KeyMetadata::new_dev(
        lowered.circuit_hash(),
        artifact.metadata.noir_version.clone(),
        lowered.num_public_inputs(),
        num_constraints,
    );
    metadata.deterministic_rng_seed = args.deterministic_rng;
    fs::write(&meta_path, serde_json::to_string_pretty(&metadata)?)
        .with_context(|| format!("writing {}", meta_path.display()))?;

    println!("Wrote {}", pk_path.display());
    println!("Wrote {}", vk_path.display());
    println!("Wrote {}", meta_path.display());
    println!("\nWARNING: setup_mode = insecure-dev-mode. Do not use in production.");
    Ok(())
}
