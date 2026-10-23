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

use anyhow::{Context, Result, anyhow, bail};
use ark_bn254::G1Affine;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Compress, Validate};
use clap::{Args, Subcommand};
use rand::rngs::OsRng;

use xark_backend::ceremony::{
    Contribution, contribute, verify_chain, verify_keys_consistent_with_chain,
};
use xark_backend::keys::{Groth16Keys, KeyMetadata};
use xark_backend::ptau::parse_ptau;
use xark_prover::XarkCircuit;

use super::{load_backend_r1cs, num_public_inputs};
use crate::xark_project::XarkProject;

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
    /// Circuit crate directory (or its `target/xark/<name>/` output dir). Defaults
    /// to the current directory; the circuit is read from its `circuit.xbc`.
    #[arg(value_hint = clap::ValueHint::DirPath)]
    pub path: Option<PathBuf>,
    /// Powers-of-Tau transcript (`.ptau`, snarkjs / Hermez format) large enough
    /// for the circuit.
    #[arg(long, value_hint = clap::ValueHint::FilePath)]
    pub ptau_file: PathBuf,
    /// Optional — auto-generated via OS RNG when not supplied. Pass this to
    /// reproduce byte-identical initial keys from the same circuit + `.ptau`.
    #[arg(long, value_name = "HEX")]
    pub phase2_seed: Option<String>,
    /// Ceremony directory to create: the keys and contribution chain live here,
    /// and every later `xark ceremony` step takes it as `--ceremony-dir`.
    #[arg(long, value_hint = clap::ValueHint::DirPath)]
    pub out: PathBuf,
    /// Replace a ceremony already in `--out`, discarding its keys and every
    /// contribution (and its `metadata.json`, if finalized).
    #[arg(long)]
    pub force: bool,
}

#[derive(Args, Debug)]
pub struct ContributeArgs {
    /// The directory `xark ceremony init --out` created.
    #[arg(long, value_hint = clap::ValueHint::DirPath)]
    pub ceremony_dir: PathBuf,
    /// Human-readable label recorded in the contribution attestation.
    #[arg(long, default_value = "anonymous")]
    pub label: String,
}

#[derive(Args, Debug)]
pub struct VerifyArgs {
    /// The directory `xark ceremony init --out` created.
    #[arg(long, value_hint = clap::ValueHint::DirPath)]
    pub ceremony_dir: PathBuf,
}

#[derive(Args, Debug)]
pub struct FinalizeArgs {
    /// The directory `xark ceremony init --out` created.
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
    // Not over an existing ceremony unless asked (`--force`): that discards its
    // contributions. And then all of it goes, so a finalized one's
    // `metadata.json` (production-safe) can't survive beside fresh keys whose
    // secrets the initiator knows.
    let existing = ceremony_files(&args.out);
    if let Some(f) = existing.first()
        && !args.force
    {
        bail!(
            "{} already holds a ceremony ({}); pick a new --out directory, or pass \
             --force to discard it and every contribution",
            args.out.display(),
            f.file_name().unwrap_or_default().to_string_lossy()
        );
    }
    // The build's `circuit.xbc`, loaded as `xark setup` does.
    let project = XarkProject::resolve(args.path.clone())?;
    crate::cli::require_bn254(&project.circuit_xbc())?;
    let (prog, hash) = load_backend_r1cs(&project.circuit_xbc())?;
    let digest = fs::read(project.circuit_xbc())
        .ok()
        .map(|b| super::r1cs_digest(&b));
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

    let src = xark_groth16::ProgramSource::new(circuit.prog());
    let keys = xark_backend::ptau::setup_from_ptau(&src, &ptau, &seed_arr)
        .map_err(|e| anyhow!("phase-2 setup failed: {e}"))?;

    // The new keys exist, so `--force` can now clear the old ceremony.
    for f in &existing {
        fs::remove_file(f).with_context(|| format!("removing {}", f.display()))?;
    }
    if !existing.is_empty() {
        println!(
            "Discarded the ceremony in {} ({} files)",
            args.out.display(),
            existing.len()
        );
    }
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
            "digest": digest,
            "num_public_inputs": num_pi,
        }))?,
    )?;

    println!("Initialized ceremony at {}", args.out.display());
    println!("baseline_delta_g1 recorded; 0 contributions so far.");
    Ok(())
}

fn run_contribute(args: ContributeArgs) -> Result<()> {
    let dir = &args.ceremony_dir;
    require_ceremony(dir)?;
    if dir.join("metadata.json").exists() {
        bail!(
            "{} is finalized; a contribution now would change keys its metadata.json \
             already describes",
            dir.display()
        );
    }
    let mut keys = load_keys(&dir.join("proving_key.bin"), &dir.join("verifying_key.bin"))?;
    let mut rng = OsRng;
    let contribution = contribute(&mut keys, &args.label, &mut rng)
        .map_err(|e| anyhow!("contribute failed: {e}"))?;

    let count = read_contribution_count(dir)?;
    let new_index = count + 1;

    // Everything is written under a temporary name first, then swapped in, so an
    // interrupted contribution leaves the ceremony as it was (keys, attestation
    // and count agreeing), not keys the recorded chain doesn't explain.
    let attestation = format!("contribution_{new_index:04}.json");
    let tmp = |name: &str| dir.join(format!("{name}.tmp"));
    keys.write_proving_key(&tmp("proving_key.bin"))?;
    keys.write_verifying_key(&tmp("verifying_key.bin"))?;
    fs::write(
        tmp(&attestation),
        serde_json::to_string_pretty(&contribution)?,
    )?;
    fs::write(tmp("contribution_count"), format!("{new_index}\n"))?;
    for name in [
        attestation.as_str(),
        "proving_key.bin",
        "verifying_key.bin",
        "contribution_count",
    ] {
        fs::rename(tmp(name), dir.join(name))
            .with_context(|| format!("writing {}", dir.join(name).display()))?;
    }

    println!("Contribution #{new_index} ({}) recorded.", args.label);
    println!("Updated keys + attestation written to {}", dir.display());
    Ok(())
}

fn run_verify(args: VerifyArgs) -> Result<()> {
    let dir = &args.ceremony_dir;
    require_ceremony(dir)?;
    let baseline = read_baseline_delta_g1(dir)?;
    let count = read_contribution_count(dir)?;
    // no with_capacity: count is attacker-supplied
    let mut contributions: Vec<Contribution> = Vec::new();
    for i in 1..=count {
        let path = dir.join(format!("contribution_{i:04}.json"));
        let bytes = fs::read(&path).with_context(|| format!("reading {}", path.display()))?;
        let c: Contribution = serde_json::from_slice(&bytes)?;
        contributions.push(c);
    }
    verify_chain(baseline, &contributions).map_err(|e| anyhow!("verify failed: {e}"))?;
    // bind the shipped keys to the verified chain, so a coordinator can't ship a
    // verifying key whose δ they know behind an honest-looking transcript
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
    metadata.digest = circuit_meta["digest"].as_str().map(str::to_string);
    let vk = fs::read(dir.join("verifying_key.bin")).context("reading verifying_key.bin")?;
    let vk_sha256 = super::sha256_hex(&vk);
    metadata.verifying_key_sha256 = Some(vk_sha256.clone());
    metadata.setup_mode = format!(
        "phase2-from-ptau+mpc[{} contributors]",
        read_contribution_count(dir)?
    );
    metadata.production_safe = true;
    fs::write(&meta_path, serde_json::to_string_pretty(&metadata)?)?;
    println!("Finalized; metadata.json written.");
    println!("verifying key sha256: {vk_sha256}  (pin a client's verifier to it: {{ keyHash }})");
    Ok(())
}

/// Every file a ceremony keeps in `dir` (none if it doesn't exist).
fn ceremony_files(dir: &std::path::Path) -> Vec<PathBuf> {
    const FIXED: [&str; 6] = [
        "proving_key.bin",
        "verifying_key.bin",
        "contribution_count",
        "metadata.json",
        "baseline_delta_g1.bin",
        "circuit_meta.json",
    ];
    let Ok(entries) = fs::read_dir(dir) else {
        return Vec::new();
    };
    let mut files: Vec<PathBuf> = entries
        .flatten()
        .map(|e| e.path())
        .filter(|p| {
            let name = p.file_name().unwrap_or_default().to_string_lossy();
            FIXED.contains(&name.as_ref())
                || (name.starts_with("contribution_") && name.ends_with(".json"))
                || name.ends_with(".tmp")
        })
        .collect();
    files.sort();
    files
}

fn write_contribution_count(dir: &std::path::Path, n: usize) -> Result<()> {
    fs::write(dir.join("contribution_count"), format!("{n}\n"))?;
    Ok(())
}

/// Refuse a `--ceremony-dir` that isn't one (a typo, or the wrong directory): every
/// ceremony has the `baseline_delta_g1.bin` `xark ceremony init` writes.
fn require_ceremony(dir: &std::path::Path) -> Result<()> {
    if !dir.join("baseline_delta_g1.bin").is_file() {
        bail!(
            "{} isn't a ceremony directory (it has no baseline_delta_g1.bin): start one \
             with `xark ceremony init --ptau-file <final.ptau> --out {}`",
            dir.display(),
            dir.display()
        );
    }
    Ok(())
}

fn read_contribution_count(dir: &std::path::Path) -> Result<usize> {
    let path = dir.join("contribution_count");
    let raw = fs::read_to_string(&path).with_context(|| format!("reading {}", path.display()))?;
    raw.trim()
        .parse()
        .map_err(|_| anyhow!("{} isn't a contribution count", path.display()))
}

fn read_baseline_delta_g1(dir: &std::path::Path) -> Result<G1Affine> {
    let bytes =
        fs::read(dir.join("baseline_delta_g1.bin")).context("reading baseline_delta_g1.bin")?;
    G1Affine::deserialize_with_mode(bytes.as_slice(), Compress::Yes, Validate::Yes)
        .map_err(|e| anyhow!("deserializing baseline_delta_g1.bin: {e}"))
}

/// Load a `Groth16Keys` bundle from separate proving/verifying key files.
fn load_keys(pk_path: &std::path::Path, vk_path: &std::path::Path) -> Result<Groth16Keys> {
    let missing = "the ceremony is incomplete: start it again with `xark ceremony init`";
    let by = "xark ceremony";
    let pk = super::read_artifact(pk_path, "proving key", by, missing, || {
        Groth16Keys::read_proving_key(pk_path)
    })?;
    let vk = super::read_artifact(vk_path, "verifying key", by, missing, || {
        Groth16Keys::read_verifying_key(vk_path)
    })?;
    Ok(Groth16Keys {
        proving_key: pk,
        verifying_key: vk,
    })
}
