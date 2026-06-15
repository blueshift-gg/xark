//! `xark ceremony` — phase-2 MPC ceremony driver.
//!
//! Subcommands:
//!
//! * `init` — produce the starting phase-2 keys from a `.ptau` transcript and
//!   a seed, identical to `xark setup --ptau-file... --phase2-seed...`. The
//!   initial `delta_g1` is recorded alongside the keys so verifiers can
//!   re-anchor the contribution chain later.
//! * `contribute` — apply this contributor's secret `δ_i` to the keys in
//!   place, write a `contribution_<n>.json` attestation alongside the
//!   updated keys.
//! * `verify` — walk the contribution chain against the original
//!   `delta_g1` baseline and confirm every contribution's Schnorr proof +
//!   δ-consistency pairing check.
//! * `finalize` — copy the current keys to the canonical output location,
//!   recording the chain length and producing the final `metadata.json`.

use std::fs;
use std::path::PathBuf;

use anyhow::{Context, Result, anyhow, bail};
use ark_bn254::G1Affine;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Compress, Validate};
use clap::{Args, Subcommand};
use rand::rngs::OsRng;

use xark_backend::ceremony::{Contribution, contribute, verify_chain};
use xark_backend::keys::{Groth16Keys, KeyMetadata};
use xark_backend::ptau::parse_ptau;

#[derive(Args, Debug)]
pub struct CeremonyArgs {
    #[command(subcommand)]
    pub command: CeremonyCommand,
}

#[derive(Subcommand, Debug)]
pub enum CeremonyCommand {
    /// Seed the ceremony from a `.ptau` transcript + phase-2 seed.
    Init(InitArgs),
    /// Apply one contributor's randomness in place.
    Contribute(ContributeArgs),
    /// Verify the full contribution chain.
    Verify(VerifyArgs),
    /// Mark the chain finished and write the final metadata.
    Finalize(FinalizeArgs),
}

#[derive(Args, Debug)]
pub struct InitArgs {
    #[arg(long)]
    pub artifact: PathBuf,
    #[arg(long)]
    pub ptau_file: PathBuf,
    /// Optional — auto-generated via OS RNG when not supplied. Pass this
    /// to reproduce byte-identical initial keys from the same circuit +
    /// `.ptau`.
    #[arg(long, value_name = "HEX")]
    pub phase2_seed: Option<String>,
    #[arg(long)]
    pub out: PathBuf,
}

#[derive(Args, Debug)]
pub struct ContributeArgs {
    #[arg(long)]
    pub ceremony_dir: PathBuf,
    /// Human-readable label recorded in the contribution attestation.
    #[arg(long, default_value = "anonymous")]
    pub label: String,
}

#[derive(Args, Debug)]
pub struct VerifyArgs {
    #[arg(long)]
    pub ceremony_dir: PathBuf,
}

#[derive(Args, Debug)]
pub struct FinalizeArgs {
    #[arg(long)]
    pub ceremony_dir: PathBuf,
}

pub fn run(args: CeremonyArgs) -> Result<()> {
    match args.command {
        CeremonyCommand::Init(a) => run_init(a),
        CeremonyCommand::Contribute(a) => run_contribute(a),
        CeremonyCommand::Verify(a) => run_verify(a),
        CeremonyCommand::Finalize(a) => run_finalize(a),
    }
}

fn run_init(args: InitArgs) -> Result<()> {
    use xark_acir_r1cs::artifact::parse_artifact_file;
    use xark_acir_r1cs::lower::LoweredAcirCircuit;
    use xark_backend::NoirGroth16Circuit;

    let artifact = parse_artifact_file(&args.artifact)
        .with_context(|| format!("parsing {}", args.artifact.display()))?;
    let lowered = LoweredAcirCircuit::new(artifact.clone())?;
    let circuit = NoirGroth16Circuit::for_setup(lowered.clone());

    let mut seed_arr = [0u8; 32];
    if let Some(ref seed_hex) = args.phase2_seed {
        let seed_bytes = hex::decode(seed_hex.trim_start_matches("0x"))
            .with_context(|| "decoding --phase2-seed as hex")?;
        if seed_bytes.len() != 32 {
            bail!(
                "--phase2-seed must be exactly 32 bytes (got {} bytes)",
                seed_bytes.len()
            );
        }
        seed_arr.copy_from_slice(&seed_bytes);
    } else {
        use rand::RngCore;
        OsRng.fill_bytes(&mut seed_arr);
    }

    let ptau_bytes = fs::read(&args.ptau_file)
        .with_context(|| format!("reading {}", args.ptau_file.display()))?;
    let ptau = parse_ptau(&ptau_bytes).with_context(|| "parsing.ptau file")?;

    let keys = xark_backend::ptau::setup_from_ptau(circuit, &ptau, &seed_arr)
        .map_err(|e| anyhow!("phase-2 setup failed: {e}"))?;

    fs::create_dir_all(&args.out).with_context(|| format!("creating {}", args.out.display()))?;

    // Record the initial delta_g1 baseline for verifier re-anchoring.
    let mut baseline_bytes = Vec::new();
    keys.proving_key
        .delta_g1
        .serialize_with_mode(&mut baseline_bytes, Compress::Yes)
        .map_err(|e| anyhow!("serializing baseline delta_g1: {e}"))?;
    fs::write(args.out.join("baseline_delta_g1.bin"), &baseline_bytes)?;

    keys.write_proving_key(&args.out.join("proving_key.bin"))?;
    keys.write_verifying_key(&args.out.join("verifying_key.bin"))?;
    write_contribution_count(&args.out, 0)?;

    // Stash the lowered circuit metadata for finalize().
    fs::write(
        args.out.join("circuit_meta.json"),
        serde_json::to_string_pretty(&serde_json::json!({
        "noir_version": artifact.metadata.noir_version,
        "circuit_hash": lowered.circuit_hash(),
        "num_public_inputs": lowered.num_public_inputs(),
        }))?,
    )?;

    println!("Initialized ceremony at {}", args.out.display());
    println!("baseline_delta_g1 recorded; 0 contributions so far.");
    Ok(())
}

fn run_contribute(args: ContributeArgs) -> Result<()> {
    let dir = &args.ceremony_dir;
    let mut keys = Groth16Keys::load(&dir.join("proving_key.bin"), &dir.join("verifying_key.bin"))?;
    let mut rng = OsRng;
    let contribution = contribute(&mut keys, &args.label, &mut rng)
        .map_err(|e| anyhow!("contribute failed: {e}"))?;

    let count = read_contribution_count(dir)?;
    let new_index = count + 1;

    // Persist updated keys + the new contribution attestation.
    keys.write_proving_key(&dir.join("proving_key.bin"))?;
    keys.write_verifying_key(&dir.join("verifying_key.bin"))?;

    let attestation_path = dir.join(format!("contribution_{new_index:04}.json"));
    fs::write(
        &attestation_path,
        serde_json::to_string_pretty(&contribution)?,
    )?;
    write_contribution_count(dir, new_index)?;

    println!("Contribution #{new_index} ({}) recorded.", args.label);
    println!("Updated keys + attestation written to {}", dir.display());
    Ok(())
}

fn run_verify(args: VerifyArgs) -> Result<()> {
    let dir = &args.ceremony_dir;
    let baseline = read_baseline_delta_g1(dir)?;
    let count = read_contribution_count(dir)?;
    let mut contributions: Vec<Contribution> = Vec::with_capacity(count);
    for i in 1..=count {
        let path = dir.join(format!("contribution_{i:04}.json"));
        let bytes = fs::read(&path).with_context(|| format!("reading {}", path.display()))?;
        let c: Contribution = serde_json::from_slice(&bytes)?;
        contributions.push(c);
    }
    verify_chain(baseline, &contributions).map_err(|e| anyhow!("verify failed: {e}"))?;
    println!(
        "Verified {} contribution(s); chain anchored to baseline_delta_g1.",
        count
    );
    for (i, c) in contributions.iter().enumerate() {
        println!(" contribution {:04}: {}", i + 1, c.contributor_label);
    }
    Ok(())
}

fn run_finalize(args: FinalizeArgs) -> Result<()> {
    let dir = &args.ceremony_dir;
    // Re-run verify first so finalize fails fast on tampered chains.
    run_verify(VerifyArgs {
        ceremony_dir: dir.clone(),
    })?;

    let meta_path = dir.join("metadata.json");
    let circuit_meta_raw =
        fs::read(dir.join("circuit_meta.json")).with_context(|| "reading circuit_meta.json")?;
    let circuit_meta: serde_json::Value = serde_json::from_slice(&circuit_meta_raw)?;

    let num_pi = circuit_meta["num_public_inputs"]
        .as_u64()
        .ok_or_else(|| anyhow!("circuit_meta.json missing num_public_inputs"))?
        as usize;
    let circuit_hash = circuit_meta["circuit_hash"]
        .as_str()
        .ok_or_else(|| anyhow!("circuit_meta.json missing circuit_hash"))?;
    let noir_version = circuit_meta["noir_version"]
        .as_str()
        .ok_or_else(|| anyhow!("circuit_meta.json missing noir_version"))?;

    let mut metadata = KeyMetadata::new_dev(
        circuit_hash.to_string(),
        noir_version.to_string(),
        num_pi,
        0, // unknown without re-synthesising; finalize is a chain marker.
    );
    metadata.setup_mode = format!(
        "phase2-from-ptau+mpc[{} contributors]",
        read_contribution_count(dir)?
    );
    metadata.production_safe = true;
    fs::write(&meta_path, serde_json::to_string_pretty(&metadata)?)?;
    println!("Finalized; metadata.json written.");
    Ok(())
}

fn write_contribution_count(dir: &std::path::Path, n: usize) -> Result<()> {
    fs::write(dir.join("contribution_count"), format!("{n}\n"))?;
    Ok(())
}

fn read_contribution_count(dir: &std::path::Path) -> Result<usize> {
    let raw = fs::read_to_string(dir.join("contribution_count"))
        .with_context(|| "reading contribution_count")?;
    Ok(raw.trim().parse()?)
}

fn read_baseline_delta_g1(dir: &std::path::Path) -> Result<G1Affine> {
    let bytes = fs::read(dir.join("baseline_delta_g1.bin"))
        .with_context(|| "reading baseline_delta_g1.bin")?;
    G1Affine::deserialize_with_mode(bytes.as_slice(), Compress::Yes, Validate::Yes)
        .map_err(|e| anyhow!("deserializing baseline_delta_g1.bin: {e}"))
}

// -----------------------------------------------------------------------------
// `Groth16Keys::load` shim
// -----------------------------------------------------------------------------

trait KeysLoad {
    fn load(pk_path: &std::path::Path, vk_path: &std::path::Path) -> Result<Self>
    where
        Self: Sized;
}

impl KeysLoad for Groth16Keys {
    fn load(pk_path: &std::path::Path, vk_path: &std::path::Path) -> Result<Self> {
        let pk = Groth16Keys::read_proving_key(pk_path)?;
        let vk = Groth16Keys::read_verifying_key(vk_path)?;
        Ok(Groth16Keys {
            proving_key: pk,
            verifying_key: vk,
        })
    }
}
