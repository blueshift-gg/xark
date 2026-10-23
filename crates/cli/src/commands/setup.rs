//! `xark setup` — generate Groth16 proving/verifying keys for a circuit.
//!
//! Reads the `circuit.xbc` produced by `xark build` and runs either the insecure
//! dev-mode setup (`--insecure-dev-mode`) or the production phase-2 setup from a
//! Powers-of-Tau transcript (`--ptau-file`, or one auto-detected under
//! `target/xark/<name>/`). Keys land next to the build output as `pk.bin` / `vk.bin`.

use std::fs;
use std::path::PathBuf;

use anyhow::{Context, Result, bail};
use clap::Args;
use rand::rngs::OsRng;
use rand::{CryptoRng, RngCore, SeedableRng};
use rand_chacha::ChaCha20Rng;

use ark_serialize::Compress;
use xark_backend::keys::KeyMetadata;
use xark_backend::serialization::canonical_write_to_file;
use xark_prover::XarkCircuit;

use super::{circuit_hash, load_backend_r1cs, num_public_inputs};
use crate::xark_project::XarkProject;

#[derive(Args, Debug)]
pub struct SetupArgs {
    /// Circuit crate directory (or its `target/xark/<name>/` output dir). Defaults to
    /// the current directory; paths are inferred from `target/xark/<name>/`.
    #[arg(value_hint = clap::ValueHint::DirPath)]
    pub path: Option<PathBuf>,

    /// Directory to write the keys and their metadata to (created if missing; a
    /// warning if it isn't empty). Defaults to `target/xark/<name>/`.
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
    /// `setup` auto-detects a `.ptau` in `target/xark/<name>/`, `target/xark/`, the
    /// crate root, or a `ptau/` directory in any of them.
    #[arg(long, value_name = "PATH", value_hint = clap::ValueHint::FilePath)]
    pub ptau_file: Option<PathBuf>,
    /// 32-byte randomness seed (hex) for the phase-2 `(γ, δ)` derivation.
    /// Optional — auto-generated via OS RNG when not supplied.
    #[arg(long, value_name = "HEX")]
    pub phase2_seed: Option<String>,

    /// Write the proving key UNCOMPRESSED (2× on disk) so `xark prove` skips the
    /// per-point square-root decompression on load — a large prove-time win (the
    /// decompress is ~half of prove). Default is compressed (smaller on disk /
    /// bandwidth). `xark prove` auto-detects which format the key is in.
    #[arg(long, default_value_t = false)]
    pub uncompressed: bool,

    /// Which R1CS form to generate the key for. Both prove with the streaming
    /// prover; they differ in where the rows come from.
    ///
    /// * `reduced` — the template-reduced circuit, streamed straight from
    ///   `circuit.xbc` (no extra artifact; setup skips the global minimize pass).
    /// * `minimized` — the boundary-minimized circuit (a few % smaller on some
    ///   circuits); setup also writes `r1cs.stream`, which prove streams.
    /// * `auto` (default) — `reduced` at or above 2^20 constraints, where the global
    ///   minimize costs GBs of setup memory for ~0% gain (Ed25519: 576 of 2.36M
    ///   rows); below that, `minimized` only if it shrinks the FFT domain or saves
    ///   ≥ 1% of rows or variables (sha256: 4.9%), else `reduced`.
    #[arg(long, value_enum, default_value_t = R1csForm::Auto)]
    pub r1cs_form: R1csForm,

    /// Shorthand for `--r1cs-form reduced`.
    #[arg(long, default_value_t = false, conflicts_with = "r1cs_form")]
    pub streamable: bool,

    /// QAP evaluation domain.
    ///
    /// * `smooth` — the smallest of `2^k`, `3·2^k`, `9·2^k` points. A circuit just
    ///   past a power of two gets a domain up to 44% smaller, so a smaller key and
    ///   a faster quotient FFT and `H` MSM (Ed25519: 4.19M → 2.36M points). The
    ///   verifier is unchanged, but only xark's provers (`xark prove`, xark-wasm)
    ///   can prove against the key — not snarkjs or rapidsnark. Dev-mode only: a
    ///   Powers-of-Tau transcript's Lagrange bases are radix-2.
    /// * `radix2` — `2^k` points, what every Groth16 prover expects.
    /// * `auto` (default) — `smooth`, except `radix2` for a Powers-of-Tau setup.
    #[arg(long, value_enum, default_value_t = QapDomain::Auto)]
    pub domain: QapDomain,
}

/// See [`SetupArgs::domain`].
#[derive(clap::ValueEnum, Clone, Copy, Debug, PartialEq, Eq)]
pub enum QapDomain {
    Auto,
    Radix2,
    Smooth,
}

impl QapDomain {
    /// The concrete domain kind for a setup with/without a `.ptau`.
    fn resolve(self, ptau: bool) -> xark_groth16::DomainKind {
        match self {
            QapDomain::Smooth => xark_groth16::DomainKind::Smooth,
            QapDomain::Auto if !ptau => xark_groth16::DomainKind::Smooth,
            _ => xark_groth16::DomainKind::Radix2,
        }
    }
}

/// See [`SetupArgs::r1cs_form`].
#[derive(clap::ValueEnum, Clone, Copy, Debug, PartialEq, Eq)]
pub enum R1csForm {
    Auto,
    Reduced,
    Minimized,
}

/// `auto` always picks `reduced` at or above this many (template-reduced) rows.
pub const AUTO_REDUCED_ROWS: usize = 1 << 20;
/// Below it, `minimized` must save at least this fraction of rows or variables.
const AUTO_MIN_SAVING: f64 = 0.01;

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

/// The circuit the key is generated for, the form's metadata name, and why.
/// `prog` is the template-reduced R1CS (or a debug flat build's, which is always
/// minimized).
fn keyed_circuit(
    prog: &xark_ir::R1csProgram,
    form: R1csForm,
    flat: bool,
    kind: xark_groth16::DomainKind,
) -> (XarkCircuit, &'static str, String) {
    let domain =
        |p: &xark_ir::R1csProgram| kind.size(p.constraints.len() + num_public_inputs(p) + 1);
    let reduced = || XarkCircuit::for_setup_preminimized(prog.clone());
    match form {
        _ if flat => (
            XarkCircuit::for_setup(prog.clone()),
            "minimized",
            "debug flat build".into(),
        ),
        R1csForm::Reduced => (reduced(), "reduced", "requested".into()),
        R1csForm::Minimized => (
            XarkCircuit::for_setup(prog.clone()),
            "minimized",
            "requested".into(),
        ),
        R1csForm::Auto if prog.constraints.len() >= AUTO_REDUCED_ROWS => (
            reduced(),
            "reduced",
            format!(
                "{} constraints ≥ 2^20: the global minimize isn't worth its setup memory",
                prog.constraints.len()
            ),
        ),
        R1csForm::Auto => {
            let min = XarkCircuit::for_setup(prog.clone());
            let (r, m) = (prog, min.prog());
            let saved = |a: usize, b: usize| 1.0 - b as f64 / a.max(1) as f64;
            let rows = saved(r.constraints.len(), m.constraints.len());
            let vars = saved(r.variables.len(), m.variables.len());
            let smaller_domain = domain(m) < domain(r);
            let why = format!(
                "minimize saves {:.1}% rows, {:.1}% variables{}",
                rows * 100.0,
                vars * 100.0,
                if smaller_domain {
                    ", shrinks the FFT domain"
                } else {
                    ""
                }
            );
            if smaller_domain || rows.max(vars) >= AUTO_MIN_SAVING {
                (min, "minimized", why)
            } else {
                (reduced(), "reduced", why)
            }
        }
    }
}

/// Write `r1cs.stream` (the keyed circuit, row-file encoded) for a `minimized`
/// key, so prove can stream it. Best-effort, like the cache.
fn write_row_file(out_dir: &std::path::Path, fingerprint: &str, circuit: &XarkCircuit) {
    let bytes = xark_ir::r1cs_stream::encode(fingerprint, circuit.prog());
    let path = out_dir.join("r1cs.stream");
    match fs::write(&path, &bytes) {
        Ok(()) => println!("Wrote {}", path.display()),
        Err(e) => eprintln!("warning: could not write {}: {e}", path.display()),
    }
}

/// The circuit the key is generated for, as a row source.
enum Keyed {
    /// The template-reduced rows, streamed straight from `circuit.xbc`.
    Bytecode(xark_groth16::BytecodeSource),
    /// The boundary-minimized program (small circuits, or a debug flat build).
    Program(XarkCircuit),
}

impl Keyed {
    fn with_source<T>(&self, f: impl FnOnce(&dyn xark_groth16::ConstraintSource) -> T) -> T {
        match self {
            Keyed::Bytecode(src) => f(src),
            Keyed::Program(circ) => f(&xark_groth16::ProgramSource::new(circ.prog())),
        }
    }
}

/// Decide the key form and build its row source. The bytecode's row count picks
/// `reduced` for large circuits without ever expanding them; only a candidate for
/// `minimized` (or a debug flat build) is materialized, for the minimize
/// pass. Returns `(source, form, reason, fingerprint, reduced rows, public inputs,
/// QAP domain kind)`.
#[allow(clippy::type_complexity)]
fn plan_keyed(
    args: &SetupArgs,
    project: &XarkProject,
    form: R1csForm,
    ptau: bool,
) -> Result<(
    Keyed,
    &'static str,
    String,
    String,
    usize,
    usize,
    xark_groth16::DomainKind,
)> {
    let xbc = project.circuit_xbc();
    let flat = super::dbg_flag("XARK_FLAT_MINIMIZE") || super::dbg_flag("XARK_NO_MINIMIZE");
    if xbc.exists() && !flat {
        let kind = args.domain.resolve(ptau);
        let bytes = fs::read(&xbc).with_context(|| format!("reading {}", xbc.display()))?;
        if !super::is_function_artifact(&bytes) {
            bail!(
                "{} is not a current circuit artifact — rebuild with `xark build`",
                xbc.display()
            );
        }
        let hash = super::sha256_hex(&bytes);
        let src = xark_groth16::BytecodeSource::new(&bytes).map_err(|e| anyhow::anyhow!(e))?;
        let rows = xark_groth16::ConstraintSource::num_constraints(&src);
        let num_pi = xark_groth16::ConstraintSource::layout(&src).num_instance() - 1;
        let reduced = |why: String| {
            Ok((
                Keyed::Bytecode(src),
                "reduced",
                why,
                hash.clone(),
                rows,
                num_pi,
                kind,
            ))
        };
        return match form {
            R1csForm::Reduced => reduced("requested".into()),
            R1csForm::Auto if rows >= AUTO_REDUCED_ROWS => reduced(format!(
                "{rows} constraints ≥ 2^20: the global minimize isn't worth its setup memory"
            )),
            _ => {
                let prog = xark_ir::function_decode::expand_function_blob_reduced(&bytes)
                    .map_err(|e| anyhow::anyhow!(e))?
                    .into_r1cs();
                let (circuit, name, why) = keyed_circuit(&prog, form, false, kind);
                if name == "reduced" {
                    reduced(why)
                } else {
                    Ok((Keyed::Program(circuit), name, why, hash, rows, num_pi, kind))
                }
            }
        };
    }
    // A debug flat build (`XARK_FLAT_MINIMIZE` / `XARK_NO_MINIMIZE`): materialized.
    let (prog, hash) = load_backend_r1cs(&xbc)?;
    let (rows, num_pi) = (prog.constraints.len(), num_public_inputs(&prog));
    let kind = args.domain.resolve(ptau);
    let (circuit, name, why) = keyed_circuit(&prog, form, true, kind);
    Ok((Keyed::Program(circuit), name, why, hash, rows, num_pi, kind))
}

pub fn run(args: SetupArgs) -> Result<()> {
    let project = XarkProject::resolve(args.path.clone())?;
    // Build first if there's no build yet; keys for a circuit older than its source
    // would prove the wrong thing.
    crate::cli::build_if_needed(&project.xark_dir, true)?;
    let out_dir = args.out.clone().unwrap_or_else(|| project.xark_dir.clone());
    let prof = super::dbg_flag("XARK_BUILD_TIME");
    let form = if args.streamable {
        R1csForm::Reduced
    } else {
        args.r1cs_form
    };

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
    if ptau_path.is_some() && args.domain == QapDomain::Smooth {
        bail!(
            "--domain smooth is dev-mode only: a Powers-of-Tau transcript's Lagrange bases \
             are for 2^k domains (use --insecure-dev-mode, or --domain radix2)"
        );
    }
    if args.deterministic_rng.is_some() && !args.insecure_dev_mode {
        bail!("--deterministic-rng requires --insecure-dev-mode");
    }
    // No `.ptau` and no explicit `--insecure-dev-mode`: fall back to insecure
    // dev-mode so the common `xark build && xark setup && xark prove` loop just
    // works. A real `--ptau-file` still runs production phase-2.
    let dev_fallback = ptau_path.is_none() && !args.insecure_dev_mode;

    let t_load = std::time::Instant::now();
    let (keyed, form_name, why, hash, num_constraints, num_pi, kind) =
        plan_keyed(&args, &project, form, ptau_path.is_some())?;
    println!("R1CS form: {form_name} ({why})");
    if prof {
        eprintln!(
            "SETUP_TIME: load+plan           = {:.2}s",
            t_load.elapsed().as_secs_f64()
        );
    }

    // `--out` names a directory of its own: anything already in it may be a key
    // (or more) this setup replaces.
    if args.out.is_some() {
        super::warn_if_not_empty(&out_dir, "keys");
    }
    fs::create_dir_all(&out_dir)
        .with_context(|| format!("creating output dir {}", out_dir.display()))?;
    let pk_path = out_dir.join("pk.bin");
    let vk_path = out_dir.join("vk.bin");
    let meta_path = out_dir.join("metadata.json");

    if let Keyed::Program(circuit) = &keyed {
        circuit
            .validate()
            .map_err(|e| anyhow::anyhow!("malformed circuit: {e}"))?;
        // Marked with the digest, not the file's hash: another build of the same
        // circuit (another Rust version) keeps using the rows.
        let digest = fs::read(project.circuit_xbc())
            .map(|b| super::r1cs_digest(&b))
            .unwrap_or_else(|_| hash.clone());
        write_row_file(&out_dir, &digest, circuit);
    }
    let compress = if args.uncompressed {
        Compress::No
    } else {
        Compress::Yes
    };
    // Keys and metadata are written under temporary names and swapped in at the
    // end, so a failed or interrupted setup never leaves a new key beside old
    // metadata (which could mark a dev key `production_safe`).
    let tmp = |p: &std::path::Path| {
        p.with_extension(format!(
            "{}.tmp",
            p.extension().and_then(|e| e.to_str()).unwrap_or_default()
        ))
    };
    let (pk_tmp, vk_tmp, meta_tmp) = (tmp(&pk_path), tmp(&vk_path), tmp(&meta_path));
    let pk_out = || -> Result<std::io::BufWriter<fs::File>> {
        let f =
            fs::File::create(&pk_tmp).with_context(|| format!("creating {}", pk_tmp.display()))?;
        Ok(std::io::BufWriter::with_capacity(1 << 20, f))
    };
    let mut metadata = KeyMetadata::new_dev(hash, num_pi, num_constraints);
    metadata.digest = fs::read(project.circuit_xbc())
        .ok()
        .map(|b| super::r1cs_digest(&b));
    metadata.r1cs_form = Some(form_name.to_string());
    let rows = keyed.with_source(|src| src.num_constraints() + src.layout().num_instance());
    let domain_size = kind.size(rows);
    metadata.qap_domain_size = Some(domain_size);
    // A smooth domain of `2^k` points is the radix-2 one: only a smaller,
    // mixed-radix one needs xark's provers.
    let radix2 = xark_groth16::DomainKind::Radix2.size(rows);
    if domain_size != radix2 {
        println!(
            "QAP domain: {domain_size} points (radix-2 would be {radix2}); only xark's provers \
             can prove against this key (`--domain radix2` for snarkjs / rapidsnark)"
        );
    }

    // Keys are generated from the streamed rows and written vector by vector:
    // neither the constraint system nor the proving key is ever held whole.
    let t_keygen = std::time::Instant::now();
    let vk = if let Some(ref ptau_file) = ptau_path {
        // Production phase-2 path.
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
        drop(ptau_bytes);
        let vk = keyed.with_source(|src| -> Result<_> {
            xark_backend::ptau::validate_for_circuit(
                &ptau,
                src.num_constraints(),
                src.layout().num_instance(),
            )
            .map_err(|e| anyhow::anyhow!("phase-2 setup failed: {e}"))?;
            let powers = xark_groth16::setup::PtauPowers {
                tau_g1: &ptau.tau_g1,
                tau_g2: &ptau.tau_g2,
                alpha_tau_g1: &ptau.alpha_tau_g1,
                beta_tau_g1: &ptau.beta_tau_g1,
                beta_g2: ptau.beta_g2,
            };
            xark_groth16::setup::phase2_setup(src, &powers, &seed_arr, pk_out()?, compress)
                .map_err(|e| anyhow::anyhow!("phase-2 setup failed: {e}"))
        })?;
        metadata.setup_mode = "phase2-from-ptau".into();
        metadata.production_safe = true;
        // commit to the (to-be-discarded) phase-2 seed for audit; never keep the seed
        metadata.phase2_seed_hash = Some(circuit_hash(&phase2_seed_hex));
        metadata.ptau_source = ptau_file
            .file_name()
            .and_then(|s| s.to_str())
            .map(|s| s.to_string());
        vk
    } else {
        // Dev-mode path. Only explicit `--deterministic-rng <n>` makes the key
        // reproducible; the no-`.ptau` fallback uses OsRng (a fixed seed would make
        // every dev key byte-identical with a known trapdoor).
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
        metadata.deterministic_rng_seed = args.deterministic_rng;
        keyed.with_source(|src| -> Result<_> {
            xark_groth16::setup::dev_setup(src, &mut rng, pk_out()?, compress, kind)
                .map_err(|e| anyhow::anyhow!("setup failed: {e}"))
        })?
    };
    if prof {
        eprintln!(
            "SETUP_TIME: keygen+write        = {:.2}s",
            t_keygen.elapsed().as_secs_f64()
        );
    }
    drop(keyed);

    canonical_write_to_file(&vk, &vk_tmp)?;
    let vk_sha256 = super::sha256_hex(&fs::read(&vk_tmp)?);
    metadata.verifying_key_sha256 = Some(vk_sha256.clone());
    fs::write(&meta_tmp, serde_json::to_string_pretty(&metadata)?)
        .with_context(|| format!("writing {}", meta_tmp.display()))?;
    // The old metadata goes first: until the new one is in place, the keys have
    // none, which every command reads as "not production-safe".
    match fs::remove_file(&meta_path) {
        Err(e) if e.kind() != std::io::ErrorKind::NotFound => {
            return Err(e).with_context(|| format!("removing {}", meta_path.display()));
        }
        _ => {}
    }
    for (from, to) in [
        (&pk_tmp, &pk_path),
        (&vk_tmp, &vk_path),
        (&meta_tmp, &meta_path),
    ] {
        fs::rename(from, to).with_context(|| format!("writing {}", to.display()))?;
    }

    println!("Wrote {}", pk_path.display());
    println!("Wrote {}", vk_path.display());
    println!("Wrote {}", meta_path.display());
    println!(
        "verifying key sha256: {vk_sha256}  {}",
        crate::style::dim("# pin a client's verifier to it: { keyHash }")
    );
    if ptau_path.is_some() {
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
    } else {
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
    }
    // Keys written elsewhere (`--out`): `xark prove` must be pointed at them.
    let key = (pk_path != project.proving_key()).then_some(pk_path.as_path());
    print_next_steps(&project, &args.path, key);
    Ok(())
}

fn print_next_steps(project: &XarkProject, path: &Option<PathBuf>, key: Option<&std::path::Path>) {
    // Only the *declared* inputs — never the witnesses the solver derives (e.g.
    // `to_bits` range-check bits). `circuit.xbc`'s header lists them, in order, so
    // nothing is expanded.
    let names: Vec<String> = match fs::read(project.circuit_xbc()) {
        Ok(bytes) if super::is_function_artifact(&bytes) => {
            xark_ir::function_decode::decode_input_vars(&bytes)
                .into_iter()
                .map(|v| v.name)
                .collect()
        }
        _ => Vec::new(),
    };
    let name_refs: Vec<&str> = names.iter().map(String::as_str).collect();
    let p = super::path_arg(path);
    // From `schema.json`: one entry per declared input, in its natural form (a hash's
    // `0x…` bytes, not its leaves). Short: inline; long: a file to fill in.
    let hint = match super::load_schema(&project.xark_dir).map(|s| s.summary()) {
        Some(inputs) if !inputs.is_empty() => {
            // In declaration order (a `serde_json::Map` would sort the keys).
            let entries: Vec<String> = inputs
                .iter()
                .map(|i| format!("{:?}: {}", i.name, i.template))
                .collect();
            let inline = format!("{{{}}}", entries.join(", "));
            if inline.len() <= 100 {
                format!("--inputs '{inline}'")
            } else {
                let file = project.xark_dir.join("inputs.example.json");
                let text = format!("{{\n  {}\n}}\n", entries.join(",\n  "));
                match fs::write(&file, text) {
                    Ok(()) => {
                        let cwd = std::env::current_dir().unwrap_or_default();
                        let shown = file.strip_prefix(&cwd).unwrap_or(&file);
                        format!("--inputs {}", shown.display())
                    }
                    Err(_) => super::inputs_hint(&name_refs),
                }
            }
        }
        _ => super::inputs_hint(&name_refs),
    };
    let key = key.map_or_else(String::new, |k| {
        format!(" --proving-key {}", super::shown(k))
    });
    println!(
        "\n{}",
        crate::style::next_steps(&[(
            format!("xark prove {p}{key} {hint}"),
            "solve the witness and produce a proof",
        )])
    );
}
