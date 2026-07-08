//! `xark ceremony` — phase-2 MPC ceremony driver.
//!
//! Subcommands:
//!
//! * `init` — produce the starting phase-2 keys from a `.ptau` transcript and a
//!   seed, identical to `xark setup --ptau-file … --phase2-seed …`. The initial
//!   `delta_g1` is recorded so verifiers can re-anchor the contribution chain.
//! * `contribute` — apply this contributor's secret `δ_i` to the keys in place,
//!   writing a `contribution_<n>.json` attestation.
//! * `verify` — walk the contribution chain against the original `delta_g1`
//!   baseline and confirm every Schnorr proof + δ-consistency pairing check.
//! * `finalize` — verify, then write the final `metadata.json`.

use std::fs;
use std::path::PathBuf;

use anyhow::{anyhow, bail, Context, Result};
use ark_bn254::G1Affine;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Compress, Validate};
use clap::{Args, Subcommand};
use rand::rngs::OsRng;

use xark_backend::ceremony::{
    contribute, verify_chain, verify_keys_consistent_with_chain, Contribution,
};
use xark_backend::keys::{Groth16Keys, KeyMetadata};
use xark_backend::ptau::parse_ptau;
use xark_prover::XarkCircuit;

use super::{circuit_hash, load_r1cs, num_public_inputs};

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
    /// Path to `r1cs.json` (produced by `xark build`).
    #[arg(long, value_hint = clap::ValueHint::FilePath)]
    pub r1cs: PathBuf,
    #[arg(long, value_hint = clap::ValueHint::FilePath)]
    pub ptau_file: PathBuf,
    /// Optional — auto-generated via OS RNG when not supplied. Pass this to
    /// reproduce byte-identical initial keys from the same circuit + `.ptau`.
    #[arg(long, value_name = "HEX")]
    pub phase2_seed: Option<String>,
    #[arg(long, value_hint = clap::ValueHint::DirPath)]
    pub out: PathBuf,
}

#[derive(Args, Debug)]
pub struct ContributeArgs {
    #[arg(long, value_hint = clap::ValueHint::DirPath)]
    pub ceremony_dir: PathBuf,
    /// Human-readable label recorded in the contribution attestation.
    #[arg(long, default_value = "anonymous")]
    pub label: String,
}

#[derive(Args, Debug)]
pub struct VerifyArgs {
    #[arg(long, value_hint = clap::ValueHint::DirPath)]
    pub ceremony_dir: PathBuf,
}

#[derive(Args, Debug)]
pub struct FinalizeArgs {
    #[arg(long, value_hint = clap::ValueHint::DirPath)]
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
    let r1cs_str = fs::read_to_string(&args.r1cs)
        .with_context(|| format!("reading {}", args.r1cs.display()))?;
    let prog = load_r1cs(&args.r1cs)?;
    let hash = circuit_hash(&r1cs_str);
    let num_pi = num_public_inputs(&prog);
    let circuit = XarkCircuit::for_setup(prog);

    let mut seed_arr = [0u8; 32];
    if let Some(ref seed_hex) = args.phase2_seed {
        let seed_bytes = hex::decode(seed_hex.trim_start_matches("0x"))
            .context("decoding --phase2-seed as hex")?;
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
    let ptau = parse_ptau(&ptau_bytes).context("parsing .ptau file")?;

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

    // Stash the circuit metadata for finalize().
    fs::write(
        args.out.join("circuit_meta.json"),
        serde_json::to_string_pretty(&serde_json::json!({
            "circuit_hash": hash,
            "num_public_inputs": num_pi,
        }))?,
    )?;

    println!("Initialized ceremony at {}", args.out.display());
    println!("baseline_delta_g1 recorded; 0 contributions so far.");
    Ok(())
}

fn run_contribute(args: ContributeArgs) -> Result<()> {
    let dir = &args.ceremony_dir;
    let mut keys = load_keys(&dir.join("proving_key.bin"), &dir.join("verifying_key.bin"))?;
    let mut rng = OsRng;
    let contribution = contribute(&mut keys, &args.label, &mut rng)
        .map_err(|e| anyhow!("contribute failed: {e}"))?;

    let count = read_contribution_count(dir)?;
    let new_index = count + 1;

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
    // Not `with_capacity(count)` — `count` is attacker-supplied; the loop is
    // bounded by the contribution files that actually exist.
    let mut contributions: Vec<Contribution> = Vec::new();
    for i in 1..=count {
        let path = dir.join(format!("contribution_{i:04}.json"));
        let bytes = fs::read(&path).with_context(|| format!("reading {}", path.display()))?;
        let c: Contribution = serde_json::from_slice(&bytes)?;
        contributions.push(c);
    }
    verify_chain(baseline, &contributions).map_err(|e| anyhow!("verify failed: {e}"))?;
    // The Schnorr/δ-consistency chain proves a valid randomness sequence over
    // the baseline δ·G1, but on its own says NOTHING about the keys this
    // ceremony ships. Bind them: confirm proving_key.bin/verifying_key.bin are
    // the keys the chain actually produced, so a coordinator can't run an
    // honest-looking transcript yet ship a verifying key whose δ they know.
    let keys = load_keys(&dir.join("proving_key.bin"), &dir.join("verifying_key.bin"))
        .context("loading ceremony keys to bind them to the transcript")?;
    verify_keys_consistent_with_chain(&keys, baseline, &contributions)
        .map_err(|e| anyhow!("verify failed: {e}"))?;
    println!(
        "Verified {count} contribution(s); chain anchored to baseline_delta_g1 \
         and bound to the shipped keys."
    );
    for (i, c) in contributions.iter().enumerate() {
        println!("  contribution {:04}: {}", i + 1, c.contributor_label);
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
        fs::read(dir.join("circuit_meta.json")).context("reading circuit_meta.json")?;
    let circuit_meta: serde_json::Value = serde_json::from_slice(&circuit_meta_raw)?;

    let num_pi = circuit_meta["num_public_inputs"]
        .as_u64()
        .ok_or_else(|| anyhow!("circuit_meta.json missing num_public_inputs"))?
        as usize;
    let circuit_hash = circuit_meta["circuit_hash"]
        .as_str()
        .ok_or_else(|| anyhow!("circuit_meta.json missing circuit_hash"))?;

    let mut metadata = KeyMetadata::new_dev(circuit_hash.to_string(), num_pi, 0);
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
    let raw =
        fs::read_to_string(dir.join("contribution_count")).context("reading contribution_count")?;
    Ok(raw.trim().parse()?)
}

fn read_baseline_delta_g1(dir: &std::path::Path) -> Result<G1Affine> {
    let bytes =
        fs::read(dir.join("baseline_delta_g1.bin")).context("reading baseline_delta_g1.bin")?;
    G1Affine::deserialize_with_mode(bytes.as_slice(), Compress::Yes, Validate::Yes)
        .map_err(|e| anyhow!("deserializing baseline_delta_g1.bin: {e}"))
}

/// Load a `Groth16Keys` bundle from separate proving/verifying key files.
fn load_keys(pk_path: &std::path::Path, vk_path: &std::path::Path) -> Result<Groth16Keys> {
    let pk = Groth16Keys::read_proving_key(pk_path)?;
    let vk = Groth16Keys::read_verifying_key(vk_path)?;
    Ok(Groth16Keys {
        proving_key: pk,
        verifying_key: vk,
    })
}
