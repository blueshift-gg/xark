//! `xark prove` — produce a Groth16 proof for a built circuit.
//!
//! Reads the built `circuit.xbc`, solves the witness from the `--inputs` values,
//! and proves with `xark-groth16`'s streaming prover against the proving key
//! `xark setup` wrote (neither the R1CS nor the key is ever fully in memory). The
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
use xark_backend::serialization::write_public_inputs;
use xark_groth16::{ConstraintSource, PkSource};
use xark_prover::{XarkCircuit, fr_from_decimal};

use super::{resolve_input_ids, setup, stream_soundness};
use crate::xark_project::XarkProject;

#[derive(Args, Debug)]
pub struct ProveArgs {
    /// Circuit crate directory (or its `target/xark/<name>/` output dir). Defaults to
    /// the current directory; paths are inferred from `target/xark/<name>/`.
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

    /// Proving key. Inferred as `target/xark/<name>/pk.bin` when omitted.
    #[arg(long, value_hint = clap::ValueHint::FilePath)]
    pub proving_key: Option<PathBuf>,
    /// Directory to write the proof (`proof.bin`) and its public inputs
    /// (`public_inputs.bin`) to (created if missing; a warning if it isn't empty).
    /// Defaults to `target/xark/<name>/`.
    #[arg(long, value_hint = clap::ValueHint::DirPath)]
    pub out: Option<PathBuf>,
    /// Reproducible-randomness escape hatch for test fixtures **only**. Groth16
    /// proof randomness blinds the witness — making it reproducible leaks
    /// information about the witness across proofs.
    #[arg(long, value_name = "SEED")]
    pub deterministic_rng: Option<u64>,
    /// Warm the caches that make later proofs against this key faster. On a miss,
    /// write: the decoded proving key (`pk.decoded.bin`, uncompressed: later
    /// proofs skip point decompression — Ed25519 prove ~2.3× faster, at 2× the
    /// key's disk size), and for a minimized key without one, its `r1cs.stream`
    /// (skips the minimize). A current cache is always used regardless of this
    /// flag; the flag only controls *writing* it.
    /// Ideal for producing many proofs.
    #[arg(long, default_value_t = false)]
    pub cache: bool,

    /// Keep a single domain-sized vector in memory during
    /// the quotient step by parking the others in a temp file next to the proof
    /// (rows are streamed once more). For proving the largest circuits on small
    /// machines.
    #[arg(long, default_value_t = false)]
    pub low_memory: bool,
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
    let pk_path = args
        .proving_key
        .clone()
        .unwrap_or_else(|| project.proving_key());
    let out_dir = args.out.clone().unwrap_or_else(|| project.xark_dir.clone());
    let proof_out = out_dir.join("proof.bin");

    // Auto-pipeline: let a newcomer `xark prove` straight after writing a
    // circuit. Builds and/or sets up on demand, but only when the default
    // artifacts are *absent* — it never overwrites an existing build or key, so
    // it just replaces a "run build first" error with actually doing it.
    autobuild_and_setup(&args, &project, &pk_path)?;

    // `PROVE_TIME=1` prints a coarse phase breakdown (solve / prove) so the real
    // bottleneck is measured, not assumed.
    let timing = super::dbg_flag("PROVE_TIME");
    let xbc = project.circuit_xbc();
    // Inputs come from `--inputs`: inline JSON or a file path (agnostic).
    let inputs = match &args.inputs {
        Some(arg) => super::read_inputs(&project.xark_dir, arg)?,
        None => Default::default(),
    };
    let sources = crate::commands::load_sources(&project.xark_dir);

    // The streaming prover: neither the R1CS nor the key is ever fully in memory.
    // A `reduced` key streams rows straight from the bytecode; a `minimized` key
    // streams them from the `r1cs.stream` setup wrote next to it (rebuilt from
    // `circuit.xbc` if missing or unreadable). A key whose metadata doesn't say
    // (a ceremony's) is told apart by its size.
    let row_file = pk_path.with_file_name("r1cs.stream");
    let kind = match key_form(&pk_path).as_deref() {
        Some("reduced") => StreamKind::Bytecode,
        Some("minimized") => StreamKind::RowFile(row_file),
        _ if row_file.exists() => StreamKind::RowFile(row_file),
        _ => {
            let bytes = fs::read(&xbc)
                .with_context(|| format!("reading {} (run `xark build` first?)", xbc.display()))?;
            let src = xark_groth16::BytecodeSource::new(&bytes).map_err(|e| anyhow::anyhow!(e))?;
            let pk = super::read_artifact(
                &pk_path,
                "proving key",
                "xark setup",
                "run `xark setup` first?",
                || xark_groth16::SerializedPk::open(&pk_path),
            )?;
            if pk.header().a_len == src.layout().num_vars() {
                StreamKind::Bytecode
            } else {
                StreamKind::RowFile(row_file)
            }
        }
    };
    let (proof, public) = prove_streaming(
        &args,
        &xbc,
        &pk_path,
        kind,
        &inputs,
        sources.as_ref(),
        timing,
    )?;
    write_outputs(&args, &proof_out, &out_dir, proof, public)
}

/// The prover RNG: OS randomness, or — test fixtures only — a fixed seed (refused
/// for production keys: reproducible randomness breaks zero-knowledge).
fn prove_rng(args: &ProveArgs, pk_path: &std::path::Path) -> Result<ProveRng> {
    if args.deterministic_rng.is_some() && key_is_production_safe(pk_path) {
        anyhow::bail!(
            "--deterministic-rng cannot be used with a production key \
             (metadata.production_safe = true): reproducible prover randomness breaks \
             zero-knowledge. Remove the flag to prove with OS randomness."
        );
    }
    Ok(match args.deterministic_rng {
        Some(seed) => {
            eprintln!(
                "WARN: --deterministic-rng makes proofs reproducible; do not use in production."
            );
            ProveRng::Det(ChaCha20Rng::seed_from_u64(seed))
        }
        None => ProveRng::Os(OsRng),
    })
}

/// The R1CS form the key was generated for (`metadata.json` `r1cs_form`):
/// `"reduced"`, `"minimized"`, or `None` for a key that predates the field
/// (minimized).
fn key_form(pk_path: &std::path::Path) -> Option<String> {
    key_meta(pk_path, "r1cs_form").and_then(|f| f.as_str().map(str::to_string))
}

/// Field `key` of the `metadata.json` next to the proving key.
fn key_meta(pk_path: &std::path::Path, key: &str) -> Option<serde_json::Value> {
    let dir = pk_path.parent()?;
    fs::read_to_string(dir.join("metadata.json"))
        .ok()
        .and_then(|s| serde_json::from_str::<serde_json::Value>(&s).ok())
        .and_then(|mut v| v.get_mut(key).map(serde_json::Value::take))
}

/// Where the streaming prover reads constraint rows from.
enum StreamKind {
    /// The template-reduced rows, expanded from `circuit.xbc`.
    Bytecode,
    /// The keyed rows from an `r1cs.stream` row file.
    RowFile(PathBuf),
}

/// The streaming path: solve by streaming the hint
/// program, then prove with `xark-groth16` — rows expanded window-by-window from
/// the bytecode and the key read chunk-by-chunk, so neither the R1CS nor the key
/// is ever resident. Self-verified against the key's `vk`.
fn prove_streaming(
    args: &ProveArgs,
    xbc: &std::path::Path,
    pk_path: &std::path::Path,
    kind: StreamKind,
    inputs: &BTreeMap<String, String>,
    sources: Option<&xark_ir::SourceMap>,
    timing: bool,
) -> Result<(xark_groth16::Proof<ark_bn254::Bn254>, Vec<ark_bn254::Fr>)> {
    let t = std::time::Instant::now();
    let bytes = std::fs::read(xbc).with_context(|| format!("reading {}", xbc.display()))?;
    let fingerprint = super::sha256_hex(&bytes);
    // A key made for another circuit can't prove this one: say so, rather than
    // failing the self-verification below. One made from another build of the same
    // circuit (another Rust version) fits.
    match super::key_fit(pk_path, &bytes) {
        super::KeyFit::Different => anyhow::bail!(
            "the proving key {} was made for a different build of the circuit \
             (the circuit changed since `xark setup`): run `xark setup` again",
            pk_path.display()
        ),
        super::KeyFit::SameCircuit => eprintln!(
            "note: {} was made from another build of this circuit (the same constraints, \
             compiled differently, e.g. by another Rust version); proving with it",
            pk_path.display()
        ),
        super::KeyFit::Same => {}
    }
    // Whether the rows came without re-running the minimize (the `cached=` marker).
    let mut cached = true;
    let src: Box<dyn ConstraintSource> = match kind {
        StreamKind::Bytecode => {
            Box::new(xark_groth16::BytecodeSource::new(&bytes).map_err(|e| anyhow::anyhow!(e))?)
        }
        StreamKind::RowFile(path) => {
            let read = std::fs::read(&path)
                .map_err(|e| e.to_string())
                .and_then(|rf| xark_groth16::RowFileSource::new(rf).map_err(|e| e.to_string()))
                .and_then(|src| {
                    if xark_ir::function_decode::row_file_fits(
                        src.file().fingerprint(),
                        &fingerprint,
                        &bytes,
                    ) {
                        Ok(src)
                    } else {
                        Err("written for a different circuit.xbc".into())
                    }
                });
            match read {
                Ok(src) => Box::new(src),
                Err(why) => {
                    // Rebuild the minimized circuit exactly as `xark setup` keyed it;
                    // `--cache` writes it back for the next proof.
                    eprintln!(
                        "note: {} unusable ({why}); rebuilding the minimized circuit",
                        path.display()
                    );
                    cached = false;
                    let reduced = xark_ir::function_decode::expand_function_blob_reduced(&bytes)
                        .map_err(|e| anyhow::anyhow!(e))?
                        .into_r1cs();
                    let circuit = XarkCircuit::for_setup(reduced);
                    let digest = super::r1cs_digest(&bytes);
                    let rows = xark_ir::r1cs_stream::encode(&digest, circuit.prog());
                    drop(circuit);
                    if args.cache {
                        fs::write(&path, &rows)
                            .with_context(|| format!("writing {}", path.display()))?;
                        println!("Wrote {}", path.display());
                    }
                    Box::new(
                        xark_groth16::RowFileSource::new(rows).map_err(|e| anyhow::anyhow!(e))?,
                    )
                }
            }
        }
    };
    let vars = xark_ir::function_decode::decode_input_vars(&bytes);
    let id_inputs = resolve_input_ids(&vars, inputs)?;
    drop(vars);
    let assign_fp = stream_soundness(&bytes, sources, &id_inputs)?;
    let t_solve = t.elapsed();
    let z = src.layout().assignment(|id| {
        assign_fp.get(&id).map(|v| {
            v.as_bn254_fr()
                .unwrap_or_else(|| fr_from_decimal(&v.to_decimal()))
        })
    });
    drop(assign_fp);
    let public = z[1..src.layout().num_instance()].to_vec();
    let mut pk = super::read_artifact(
        pk_path,
        "proving key",
        "xark setup",
        "run `xark setup` first?",
        || xark_groth16::SerializedPk::open(pk_path),
    )?;
    // A decoded (uncompressed) copy of a compressed key skips the per-point
    // decompression. Used only if its header — vk, β, δ, vector lengths — is
    // exactly this key's (a different setup has a different vk).
    let decoded = pk_path.with_file_name("pk.decoded.bin");
    let mut tee_tmp = None;
    if pk.is_compressed() {
        match xark_groth16::SerializedPk::open(&decoded) {
            Ok(c) if !c.is_compressed() && c.header() == pk.header() => {
                eprintln!("using decoded key cache {}", decoded.display());
                pk = c;
            }
            _ if args.cache => {
                let tmp = decoded.with_extension("bin.tmp");
                let f = fs::File::create(&tmp)
                    .with_context(|| format!("creating {}", tmp.display()))?;
                pk.tee_uncompressed(Box::new(std::io::BufWriter::with_capacity(1 << 20, f)))?;
                tee_tmp = Some(tmp);
            }
            _ => {}
        }
    }
    let mut rng = prove_rng(args, pk_path)?;
    let t_prove = std::time::Instant::now();
    let cfg = xark_groth16::ProverConfig {
        spill_dir: args.low_memory.then(|| {
            pk_path
                .parent()
                .map(std::path::Path::to_path_buf)
                .unwrap_or_else(std::env::temp_dir)
        }),
        ..xark_groth16::ProverConfig::default()
    };
    let proof = xark_groth16::prove(&*src, &z, &mut pk, &mut rng, &cfg)
        .map_err(|e| anyhow::anyhow!("streaming prove: {e}"))?;
    if let Some(tmp) = tee_tmp {
        if pk.finish_tee()? {
            fs::rename(&tmp, &decoded).with_context(|| format!("writing {}", decoded.display()))?;
            println!("Wrote {} (decoded key cache)", decoded.display());
        } else {
            let _ = fs::remove_file(&tmp);
        }
    }
    if timing {
        eprintln!(
            "PROVE_TIME: [streaming] solve={t_solve:?} prove={:?} ({} constraints) cached={cached}",
            t_prove.elapsed(),
            src.num_constraints()
        );
    }
    Ok((proof, public))
}

/// Write the proof and public inputs, and print a summary.
#[allow(clippy::too_many_arguments)]
fn write_outputs(
    args: &ProveArgs,
    proof_out: &std::path::Path,
    out_dir: &std::path::Path,
    proof: xark_groth16::Proof<ark_bn254::Bn254>,
    public: Vec<ark_bn254::Fr>,
) -> Result<()> {
    let bundle = ProofBundle {
        proof,
        public_inputs: public.clone(),
    };

    if args.out.is_some() {
        super::warn_if_not_empty(out_dir, "proof");
    }
    fs::create_dir_all(out_dir)
        .with_context(|| format!("creating output dir {}", out_dir.display()))?;
    bundle.write_proof(proof_out)?;

    // Public inputs as canonical binary (primary format for verify/export).
    let public_path = out_dir.join("public_inputs.bin");
    write_public_inputs(&public, &public_path)?;

    // Fingerprint the proof itself (SHA-256 of `proof.bin`): a stable id for
    // *this* proof, to reference or track it.
    let proof_bin =
        fs::read(proof_out).with_context(|| format!("reading {}", proof_out.display()))?;
    let proof_sha = super::sha256_hex(&proof_bin);

    println!("Wrote {}", proof_out.display());
    println!("Wrote {}", public_path.display());
    println!(
        "\n{}",
        crate::style::brand(&format!(
            "✅ Proof produced and self-checked ({} public input(s)).",
            public.len()
        ))
    );

    println!(
        "\nproof sha256:  0x{proof_sha}  {}",
        crate::style::dim("# fingerprint — copy to reference this exact proof")
    );

    let p = super::path_arg(&args.path);
    // A proof written elsewhere (`--out`), or made with another key: point
    // `verify` and `export` at them.
    let mut files = String::new();
    // The verifying key beside a `--proving-key`: `xark setup`'s or a ceremony's.
    if let Some(vk) = args
        .proving_key
        .as_ref()
        .and_then(|pk| pk.parent())
        .and_then(|d| {
            ["vk.bin", "verifying_key.bin"]
                .map(|f| d.join(f))
                .into_iter()
                .find(|vk| vk.exists())
        })
    {
        files += &format!(" --verifying-key {}", super::shown(&vk));
    }
    if args.out.is_some() {
        files += &format!(
            " --proof {} --public-inputs {}",
            super::shown(proof_out),
            super::shown(&public_path)
        );
    }
    println!(
        "\n{}",
        crate::style::next_steps(&[
            (
                format!("xark verify {p}{files}"),
                "check this proof locally"
            ),
            (
                format!("xark client {p}"),
                "generate a typed TypeScript client (prove + verify in JS)",
            ),
            (
                format!("xark export {p}{files}"),
                "generate the on-chain Solana verifier crate",
            ),
        ])
    );
    Ok(())
}

/// When `xark prove` is run before `build`/`setup`, do them on demand so the
/// first-time loop is a single command. Triggers only on *missing* default
/// artifacts; an explicit `--proving-key` path is left untouched.
fn autobuild_and_setup(
    args: &ProveArgs,
    project: &XarkProject,
    pk_path: &std::path::Path,
) -> Result<()> {
    // "Built" is signalled by `circuit.xbc`, which every build emits.
    let mut is_built = project.circuit_xbc().exists();
    if !is_built && let Some(dir) = find_crate_dir(args, project) {
        eprintln!(
            "{} no build found — running `xark build {}` first…",
            crate::style::tag(),
            dir.display()
        );
        if crate::cli::cmd_build(&[dir.display().to_string()]) != 0 {
            anyhow::bail!("auto-build failed (build the circuit with `xark build` first)");
        }
        is_built = project.circuit_xbc().exists();
    }
    // A build older than its source: rebuild, so the proof is of the circuit as it
    // is now (a key made for the old one then says to run `xark setup` again).
    if is_built {
        crate::cli::rebuild_if_stale(&project.xark_dir)?;
    }
    // If no crate dir is found, fall through: `load_r1cs` emits the usual
    // clear "run `xark build` first" error.
    if args.proving_key.is_none() && is_built && !pk_path.exists() {
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
            out: None,
            insecure_dev_mode: true,
            deterministic_rng: None,
            ptau_file: None,
            phase2_seed: None,
            uncompressed: false,
            r1cs_form: setup::R1csForm::Auto,
            streamable: false,
            domain: setup::QapDomain::Auto,
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
    if let Some(p) = &args.path
        && p.join("Cargo.toml").is_file()
    {
        return Some(p.clone());
    }
    if let Ok(cwd) = std::env::current_dir()
        && cwd.join("Cargo.toml").is_file()
    {
        return Some(cwd);
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
