//! `xark setup` — generate Groth16 proving/verifying keys for a circuit.
//!
//! Reads the `r1cs.json` produced by `xark build` and runs either the insecure
//! dev-mode setup (`--insecure-dev-mode`) or the production phase-2 setup from a
//! Powers-of-Tau transcript (`--ptau-file`, or one auto-detected under
//! `target/xark/`). Keys land next to the build output as `pk.bin` / `vk.bin`.

use std::fs;
use std::path::PathBuf;

use anyhow::{Context, Result, bail};
use clap::Args;
use rand::rngs::OsRng;
use rand::{CryptoRng, RngCore, SeedableRng};
use rand_chacha::ChaCha20Rng;

use xark_backend::serialization::vk_to_snarkjs;
use xark_backend::{keys::KeyMetadata, setup};
use xark_ir::Visibility;
use xark_prover::XarkCircuit;

use super::{circuit_hash, load_backend_r1cs, num_public_inputs, synth_err};
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
    /// Cache the minimized R1CS (`r1cs.min.wcz`, the exact circuit this key is
    /// generated from) next to the keys, so a later `xark prove` reloads it
    /// instead of re-deriving it — skipping the minimize + `validate()` (~25s on
    /// a multi-million-constraint circuit). Off by default: the cache can be large
    /// (hundreds of MB) and only pays off when you prove against this key. Best
    /// for the produce-many-proofs / production flow.
    #[arg(long, default_value_t = false)]
    pub cache: bool,
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

/// Cache the minimized R1CS (tagged with the source `circuit.xbc` fingerprint)
/// next to the keys, so `xark prove` can reload it and skip re-running the
/// identical boundary-minimize + `validate()`. Best-effort: a write failure just
/// forfeits the speedup (prove falls back to recomputing).
fn write_r1cs_cache(
    out_dir: &std::path::Path,
    fingerprint: &str,
    circuit: &XarkCircuit,
    prof: bool,
) {
    let t = std::time::Instant::now();
    let bytes = match xark_ir::r1cs_cache::serialize(fingerprint, circuit.prog()) {
        Ok(b) => b,
        Err(e) => {
            eprintln!("warning: could not encode R1CS cache: {e}");
            return;
        }
    };
    let path = out_dir.join("r1cs.min.wcz");
    if let Err(e) = fs::write(&path, &bytes) {
        eprintln!(
            "warning: could not write R1CS cache {}: {e}",
            path.display()
        );
        return;
    }
    if prof {
        eprintln!(
            "SETUP_TIME: write r1cs cache      = {:.2}s ({} bytes)",
            t.elapsed().as_secs_f64(),
            bytes.len()
        );
    }
}

pub fn run(args: SetupArgs) -> Result<()> {
    let project = XarkProject::resolve(args.path.clone())?;
    let r1cs_path = args.r1cs.clone().unwrap_or_else(|| project.r1cs_json());
    let out_dir = args.out.clone().unwrap_or_else(|| project.xark_dir.clone());

    // Prefer the self-contained `circuit.xbc` (deriving the R1CS from it); fall
    // back to `r1cs.json` for an explicit `--r1cs` or an `--emit-json` build.
    let prof = super::dbg_flag("XARK_BUILD_TIME");
    let t_load = std::time::Instant::now();
    let (prog, hash) = load_backend_r1cs(&project.circuit_xbc(), args.r1cs.as_deref(), &r1cs_path)?;
    if prof {
        eprintln!(
            "SETUP_TIME: load+expand         = {:.2}s",
            t_load.elapsed().as_secs_f64()
        );
    }
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

    // Only an *explicit* `--ptau-file` conflicts with `--insecure-dev-mode`
    // (auto-detection is skipped when `--insecure-dev-mode` is set, so any
    // `ptau_path` here under that flag came from `--ptau-file`).
    if ptau_path.is_some() && args.insecure_dev_mode {
        bail!(
            "--ptau-file (or auto-detected .ptau) and --insecure-dev-mode are mutually exclusive"
        );
    }
    // `--deterministic-rng` leaks the trapdoor, so require `--insecure-dev-mode`
    if args.deterministic_rng.is_some() && !args.insecure_dev_mode {
        bail!("--deterministic-rng requires --insecure-dev-mode");
    }
    // No `.ptau` and no explicit `--insecure-dev-mode`: rather than block, fall
    // back to insecure dev-mode with a hardcoded deterministic seed (1) so the
    // common `xark build && xark setup && xark prove` loop just works. A real
    // `--ptau-file` still runs production phase-2; a user-supplied
    // `--deterministic-rng <n>` still overrides the seed.
    let dev_fallback = ptau_path.is_none() && !args.insecure_dev_mode;

    fs::create_dir_all(&out_dir)
        .with_context(|| format!("creating output dir {}", out_dir.display()))?;
    let pk_path = out_dir.join("pk.bin");
    let vk_path = out_dir.join("vk.bin");
    let meta_path = out_dir.join("metadata.json");
    let snarkjs_vk_path = out_dir.join("snarkjs-verification_key.json");

    // Production phase-2 path.
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
        circuit
            .validate()
            .map_err(|e| anyhow::anyhow!("malformed circuit: {e}"))?;
        if args.cache {
            write_r1cs_cache(&out_dir, &hash, &circuit, prof);
        }
        let keys = xark_backend::ptau::setup_from_ptau(circuit, &ptau, &seed_arr)
            .map_err(|e| anyhow::anyhow!("phase-2 setup failed: {e}"))?;

        keys.write_proving_key(&pk_path)?;
        keys.write_verifying_key(&vk_path)?;

        let mut metadata = KeyMetadata::new_dev(hash, num_pi, num_constraints);
        metadata.setup_mode = "phase2-from-ptau".into();
        metadata.production_safe = true;
        // commit to the (to-be-discarded) phase-2 seed for audit; never keep the seed
        metadata.phase2_seed_hash = Some(circuit_hash(&phase2_seed_hex));
        metadata.ptau_source = ptau_file
            .file_name()
            .and_then(|s| s.to_str())
            .map(|s| s.to_string());
        fs::write(&meta_path, serde_json::to_string_pretty(&metadata)?)
            .with_context(|| format!("writing {}", meta_path.display()))?;

        let snarkjs_vk = vk_to_snarkjs(&keys.verifying_key, num_pi);
        fs::write(&snarkjs_vk_path, serde_json::to_string_pretty(&snarkjs_vk)?)?;

        println!("Wrote {}", pk_path.display());
        println!("Wrote {}", vk_path.display());
        println!("Wrote {}", snarkjs_vk_path.display());
        println!("Wrote {}", meta_path.display());
        println!(
            "{}",
            crate::style::warn(
                "\nphase2-from-ptau setup complete — but this was a SINGLE-PARTY phase-2 \
                 contribution. Whoever holds the phase-2 seed knows the γ/δ trapdoor and can \
                 forge proofs for this circuit. For production you MUST now securely DISCARD the \
                 seed (only its hash is recorded, in metadata.phase2_seed_hash), and the .ptau \
                 must itself come from a real multi-party phase-1 ceremony. For a fully \
                 trustless phase-2, use the multi-party `xark ceremony` flow instead."
            )
        );
        print_next_steps(&project, &args.path, &prog);
        return Ok(());
    }

    // Dev-mode path.
    // `for_setup` runs the boundary-minimize (self-reported `MINIMIZE:` line);
    // structural `validate()` on a multi-million-constraint circuit is itself a
    // non-trivial phase, so time it separately.
    let circuit = XarkCircuit::for_setup(prog.clone());
    let t_validate = std::time::Instant::now();
    circuit
        .validate()
        .map_err(|e| anyhow::anyhow!("malformed circuit: {e}"))?;
    if prof {
        eprintln!(
            "SETUP_TIME: validate             = {:.2}s",
            t_validate.elapsed().as_secs_f64()
        );
    }
    if args.cache {
        write_r1cs_cache(&out_dir, &hash, &circuit, prof);
    }
    // Only explicit `--deterministic-rng <n>` makes the key reproducible. The
    // no-`.ptau` dev fallback uses OsRng: still insecure, but a fixed seed would
    // be worse (every dev key byte-identical with a known trapdoor).
    let effective_seed = args.deterministic_rng;
    let mut rng = match effective_seed {
        Some(seed) => {
            eprintln!(
                "WARN: --deterministic-rng makes the Groth16 trapdoor recoverable from the \
                 seed; do not reuse the resulting keys outside test fixtures."
            );
            SetupRng::Det(ChaCha20Rng::seed_from_u64(seed))
        }
        None => SetupRng::Os(OsRng),
    };
    let t_keygen = std::time::Instant::now();
    let keys = setup(circuit, &mut rng).map_err(synth_err)?;
    if prof {
        eprintln!(
            "SETUP_TIME: groth16 keygen       = {:.2}s",
            t_keygen.elapsed().as_secs_f64()
        );
    }

    let t_write = std::time::Instant::now();
    keys.write_proving_key(&pk_path)?;
    keys.write_verifying_key(&vk_path)?;

    let snarkjs_vk = vk_to_snarkjs(&keys.verifying_key, num_pi);
    fs::write(&snarkjs_vk_path, serde_json::to_string_pretty(&snarkjs_vk)?)?;
    if prof {
        eprintln!(
            "SETUP_TIME: write pk+vk          = {:.2}s",
            t_write.elapsed().as_secs_f64()
        );
    }

    let mut metadata = KeyMetadata::new_dev(hash, num_pi, num_constraints);
    metadata.deterministic_rng_seed = effective_seed;
    fs::write(&meta_path, serde_json::to_string_pretty(&metadata)?)
        .with_context(|| format!("writing {}", meta_path.display()))?;

    println!("Wrote {}", pk_path.display());
    println!("Wrote {}", vk_path.display());
    println!("Wrote {}", snarkjs_vk_path.display());
    println!("Wrote {}", meta_path.display());
    println!(
        "\n{}",
        crate::style::warn(
            "⚠️  WARNING: setup_mode = insecure-dev-mode. Do not use in production."
        )
    );
    if dev_fallback {
        println!(
            "{}",
            crate::style::warn(
                "note: no .ptau found — generated an insecure single-party OsRng dev key; \
                 supply --ptau-file for production."
            )
        );
    }
    print_next_steps(&project, &args.path, &prog);
    Ok(())
}

/// Guided post-setup footer: show the exact `xark prove` command with a
/// placeholder for every declared input, so the next step is unambiguous.
fn print_next_steps(project: &XarkProject, path: &Option<PathBuf>, prog: &xark_ir::R1csProgram) {
    // Only the *declared* inputs — never the witnesses the solver derives
    // (e.g. `to_bits` range-check bits). The primitive program carries the
    // roles that tell them apart; the R1CS marks both `Private`, so falling
    // back to it (if the `circuit.xbc` can't be expanded) may over-list.
    // Declared inputs come first and in order, so that fallback is still usable.
    let names: Vec<String> = match super::load_circuit_auto(&project.circuit_xbc()).ok() {
        Some(prim) => {
            use xark_ir::primitive::VarRole;
            let mut vars: Vec<_> = prim
                .vars
                .iter()
                .filter(|v| matches!(v.role, VarRole::PublicInput | VarRole::PrivateInput))
                .collect();
            vars.sort_by_key(|v| v.id);
            vars.iter().map(|v| v.name.clone()).collect()
        }
        None => {
            let mut vars: Vec<_> = prog
                .variables
                .iter()
                .filter(|v| v.visibility != Visibility::Internal)
                .collect();
            vars.sort_by_key(|v| v.id);
            vars.iter().map(|v| v.name.clone()).collect()
        }
    };
    let name_refs: Vec<&str> = names.iter().map(String::as_str).collect();
    let hint = super::inputs_hint(&name_refs);
    let p = super::path_arg(path);
    println!(
        "\n{}",
        crate::style::next_steps(&[(
            format!("xark prove {p} {hint}"),
            "solve the witness and produce a proof",
        )])
    );
}
