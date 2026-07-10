//! `xark prove` — produce a Groth16 proof for a built circuit.
//!
//! Self-contained: loads `r1cs.json` + `circuit.json`, *solves* the witness from
//! the `--inputs` values (via the reference solver), loads the proving key
//! written by `xark setup`, and runs the shared `xark_backend` prover. The proof
//! and its public inputs are written next to the build output.

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
use xark_backend::solana::{assemble_proof_bytes_le, assemble_public_inputs_bytes_le};
use xark_backend::{keys::Groth16Keys, prove};
use xark_ir::VarId;
use xark_prover::{fr_from_decimal, XarkCircuit};

use super::{load_circuit, parse_inputs_arg, resolve_input_ids, setup, soundness_check, synth_err};
use crate::xark_project::XarkProject;

#[derive(Args, Debug)]
pub struct ProveArgs {
    /// Circuit crate directory (or its `target/xark/` output dir). Defaults to
    /// the current directory; paths are inferred from `target/xark/`.
    #[arg(value_hint = clap::ValueHint::DirPath)]
    pub path: Option<PathBuf>,

    /// Circuit inputs as inline JSON `{"name": value, …}` or a path to an input
    /// file (a JSON object, or `name = value` lines with `#` comments and blank
    /// lines ignored). Provide every public and private input the circuit
    /// declares; array elements use the flat names `xark inspect` prints, e.g.
    /// `path[0]`. One argument for both — inline for a quick proof, a file for a
    /// big witness (a 2-in/2-out JoinSplit has ~200 inputs).
    #[arg(long = "inputs", value_name = "JSON|FILE")]
    pub inputs: Option<String>,

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

    // Auto-pipeline: let a newcomer `xark prove` straight after writing a
    // circuit. Builds and/or sets up on demand, but only when the default
    // artifacts are *absent* — it never overwrites an existing build or key, so
    // it just replaces a "run build first" error with actually doing it.
    autobuild_and_setup(&args, &project, &r1cs_path, &pk_path)?;

    // Read the R1CS text once: parse it here, and reuse the same text for the
    // bundle's circuit hash below (no second read, no silent empty-string hash).
    let r1cs_str = std::fs::read_to_string(&r1cs_path)
        .with_context(|| format!("reading {} (run `xark build` first?)", r1cs_path.display()))?;
    let prog = xark_ir::json::from_json(&r1cs_str)
        .with_context(|| format!("parsing {}", r1cs_path.display()))?;
    let prim = load_circuit(&circuit_path)?;
    // Inputs come from `--inputs`: inline JSON or a file path (agnostic).
    let inputs = match &args.inputs {
        Some(arg) => parse_inputs_arg(arg)?,
        None => Default::default(),
    };

    // Resolve input names → variable ids for the solver (shared with `check`).
    let id_inputs = resolve_input_ids(&prim, &inputs)?;

    // Solve the witness, then run the shared under-constrained soundness gate.
    // This is the *witness-based* check: it needs the solved assignment (hence
    // it runs here, before any key-loading / synthesis), and rejects circuits
    // with a derived variable the constraints fail to pin uniquely. It returns
    // the solved assignment on success. Pass the R1CS + best-effort profile so an
    // unsatisfied witness names the failing constraint (and its source line).
    let profile = crate::commands::load_profile(&project.xark_dir);
    let assign_fp = soundness_check(&prim, &prog, profile.as_ref(), &id_inputs)?;

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

    // snarkjs-compatible proof + public inputs (reused for the standalone files
    // and embedded into the self-contained bundle below).
    let snarkjs_proof = proof_to_snarkjs(&bundle.proof);
    let snarkjs_public = public_inputs_to_snarkjs(&public);
    let snarkjs_proof_path = out_dir.join("snarkjs-proof.json");
    fs::write(
        &snarkjs_proof_path,
        serde_json::to_string_pretty(&snarkjs_proof)?,
    )?;
    let snarkjs_public_path = out_dir.join("snarkjs-public.json");
    fs::write(
        &snarkjs_public_path,
        serde_json::to_string_pretty(&snarkjs_public)?,
    )?;

    // Verifier calldata: the packed `proof (256 B) || public_inputs (N * 32 B)`
    // bytes, little-endian, that the xark on-chain verifier consumes (`A` is
    // pre-negated; see `xark_backend::solana`).
    let proof_bytes = assemble_proof_bytes_le(&bundle.proof);
    let public_bytes = assemble_public_inputs_bytes_le(&public);
    let mut calldata = Vec::with_capacity(proof_bytes.len() + public_bytes.len());
    calldata.extend_from_slice(&proof_bytes);
    calldata.extend_from_slice(&public_bytes);
    let proof_hex = format!("0x{}", hex::encode(&proof_bytes));
    let calldata_hex = format!("0x{}", hex::encode(&calldata));

    // Fingerprint the proof itself (SHA-256 of its on-chain bytes). This is a
    // stable id for *this* proof — copy it to reference/track it, and it names
    // the bundle file so distinct proofs never clobber each other.
    let proof_sha = super::sha256_hex(&proof_bytes);
    let proof_short = &proof_sha[..proof_sha.len().min(8)];

    // Self-contained, shareable proof bundle: the snarkjs proof (verify
    // off-chain) plus the verifier calldata, in one file. Named by the entry
    // name so it lines up with the generated client.
    let circuit_hash = super::circuit_hash(&r1cs_str);
    let name = project.entry_name();
    let bundle_json = serde_json::json!({
        "circuit": name,
        "circuit_hash": format!("sha256:{circuit_hash}"),
        "proof_sha256": format!("0x{proof_sha}"),
        "protocol": "groth16",
        "curve": "bn128",
        "public_signals": snarkjs_public,
        "proof": snarkjs_proof,
        "calldata": {
            "endianness": "little",
            "hex": calldata_hex,
            "proof_hex": proof_hex,
            "public_inputs_hex": format!("0x{}", hex::encode(&public_bytes)),
        },
    });
    let bundle_path = out_dir.join(format!("{name}-{proof_short}.proof.json"));
    fs::write(&bundle_path, serde_json::to_string_pretty(&bundle_json)?)
        .with_context(|| format!("writing {}", bundle_path.display()))?;

    println!("Wrote {}", proof_out.display());
    println!("Wrote {}", public_path.display());
    println!("Wrote {}", snarkjs_proof_path.display());
    println!("Wrote {}", snarkjs_public_path.display());
    println!(
        "Wrote {}  {}",
        bundle_path.display(),
        crate::style::dim("# self-contained: snarkjs proof + public + on-chain calldata")
    );
    println!(
        "\n{}",
        crate::style::brand(&format!(
            "✅ Proof produced and self-checked ({} public input(s)).",
            public.len()
        ))
    );

    // Show the proof and its fingerprint, both copy-pasteable from the terminal.
    println!(
        "\n{}",
        crate::style::brand(&format!(
            "── proof ── {} bytes, little-endian ──",
            proof_bytes.len()
        ))
    );
    println!("{proof_hex}");
    println!(
        "\nproof sha256:  0x{proof_sha}  {}",
        crate::style::dim("# fingerprint — copy to reference this exact proof")
    );

    // The packed verifier calldata (proof ‖ public), ready to hand to a verifier.
    println!(
        "\n{}",
        crate::style::brand(&format!(
            "── verifier calldata ── proof ‖ public inputs, little-endian, {} bytes ──",
            calldata.len()
        ))
    );
    println!("{calldata_hex}");
    println!(
        "{}",
        crate::style::dim("   ↑ the packed bytes your on-chain verifier consumes")
    );

    let p = super::path_arg(&args.path);
    println!(
        "\n{}",
        crate::style::next_steps(&[
            (format!("xark verify {p}"), "check this proof locally"),
            (
                format!("xark client {p}"),
                "scaffold a TypeScript client (verify + calldata)",
            ),
            (
                format!("xark export {p}"),
                "generate the on-chain Solana verifier crate",
            ),
        ])
    );
    Ok(())
}

/// When `xark prove` is run before `build`/`setup`, do them on demand so the
/// first-time loop is a single command. Triggers only on *missing* default
/// artifacts; explicit `--r1cs` / `--proving-key` paths are left untouched.
fn autobuild_and_setup(
    args: &ProveArgs,
    project: &XarkProject,
    r1cs_path: &std::path::Path,
    pk_path: &std::path::Path,
) -> Result<()> {
    if args.r1cs.is_none() && !r1cs_path.exists() {
        if let Some(dir) = find_crate_dir(args, project) {
            eprintln!(
                "{} no build found — running `xark build {}` first…",
                crate::style::tag(),
                dir.display()
            );
            if crate::cli::cmd_build(&[dir.display().to_string()]) != 0 {
                anyhow::bail!("auto-build failed (build the circuit with `xark build` first)");
            }
        }
        // If no crate dir is found, fall through: `load_r1cs` emits the usual
        // clear "run `xark build` first" error.
    }
    if args.proving_key.is_none() && r1cs_path.exists() && !pk_path.exists() {
        eprintln!(
            "{} no proving key found — generating a dev key (use `xark setup --ptau-file` \
             for production)…",
            crate::style::tag()
        );
        // Force dev-mode: the convenience loop must not silently run a production
        // phase-2 ceremony just because a stray `.ptau` is discoverable. Producing
        // a real key stays an explicit `xark setup`.
        setup::run(setup::SetupArgs {
            path: args.path.clone(),
            r1cs: args.r1cs.clone(),
            out: None,
            insecure_dev_mode: true,
            deterministic_rng: None,
            ptau_file: None,
            phase2_seed: None,
        })?;
    }
    Ok(())
}

/// Best-effort locate the circuit crate directory (holding `Cargo.toml`) to
/// auto-build: an explicit crate path, else the cwd, else walking up from the
/// resolved output dir.
fn find_crate_dir(args: &ProveArgs, project: &XarkProject) -> Option<PathBuf> {
    // Try each source independently: an explicit crate path, then the cwd, then
    // walking up from the resolved output dir. (Independent `if`s, not else-if,
    // so an explicit *non-crate* path still falls back to cwd.)
    if let Some(p) = &args.path {
        if p.join("Cargo.toml").is_file() {
            return Some(p.clone());
        }
    }
    if let Ok(cwd) = std::env::current_dir() {
        if cwd.join("Cargo.toml").is_file() {
            return Some(cwd);
        }
    }
    let mut d = project.xark_dir.clone();
    while d.pop() {
        if d.join("Cargo.toml").is_file() {
            return Some(d);
        }
    }
    None
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
