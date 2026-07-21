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
use xark_prover::{XarkCircuit, fr_from_decimal};

use super::{
    load_backend_r1cs, load_circuit_auto, parse_inputs_arg, resolve_input_ids, setup,
    soundness_check, soundness_check_r1cs, synth_err,
};
use crate::xark_project::XarkProject;

/// Load the minimized-R1CS cache at `path`, but only if it decodes and its stored
/// fingerprint matches `fingerprint` (the current `circuit.xbc` SHA-256). A
/// missing, corrupt, or stale cache returns `None` so prove recomputes instead.
fn try_load_r1cs_cache(
    path: &std::path::Path,
    fingerprint: &str,
) -> Option<xark_ir::r1cs::R1csProgram> {
    let bytes = std::fs::read(path).ok()?;
    // Fingerprint is checked (in the header) before the body is decoded, so a
    // stale or foreign cache is rejected cheaply; corrupt bytes return None too.
    xark_ir::r1cs_cache::deserialize_if_fingerprint(&bytes, fingerprint)
}

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
    /// Path to the circuit's primitive program — `circuit.xbc` (default) or a
    /// `circuit.json`. Inferred as `target/xark/…/circuit.xbc` when omitted.
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
    /// Warm the minimized-R1CS cache (`r1cs.min.wcz`): on a cache *miss*, write
    /// the minimized circuit this prove just derived so subsequent proves against
    /// the same key reload it and skip the ~25s minimize + validate. A hit (cache
    /// already present and current) is always used regardless of this flag; the
    /// flag only controls *writing* it. Ideal for producing many proofs.
    #[arg(long, default_value_t = false)]
    pub cache: bool,
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
        .unwrap_or_else(|| project.circuit_xbc());
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

    // Load the circuit + solve the witness under the soundness gate. The default
    // path — no `--r1cs`/`--circuit` overrides — expands the self-contained
    // `circuit.xbc` ONCE into a `CircuitProgram`, solves + checks directly on its
    // R1CS rows (no `to_primitive` flattening), then *moves* those rows into the
    // backend `R1csProgram` (`into_r1cs`, no clone). So a proof materializes the
    // constraint set once, not ~4×. An explicit override falls back to the JSON
    // loaders + the Expression-based gate.
    // `PROVE_TIME=1` prints a coarse phase breakdown (load+solve / key-load /
    // Groth16 prove) so the real bottleneck is measured, not assumed.
    let timing = super::dbg_flag("PROVE_TIME");
    let xbc = project.circuit_xbc();
    // Inputs come from `--inputs`: inline JSON or a file path (agnostic).
    let inputs = match &args.inputs {
        Some(arg) => parse_inputs_arg(arg)?,
        None => Default::default(),
    };
    let profile = crate::commands::load_profile(&project.xark_dir);
    // The minimized-R1CS cache `xark setup` writes next to the proving key.
    let cache_path = pk_path.with_file_name("r1cs.min.wcz");

    // Load the proving key and load+solve the circuit CONCURRENTLY: they're
    // independent (only the Groth16 prove below needs both), and the witness
    // solve is single-threaded — it leaves cores free for the parallel key
    // deserialization, so the key load is largely hidden under it.
    let t_conc = std::time::Instant::now();
    let (pk_res, circuit_res) = rayon::join(
        || {
            let tk = std::time::Instant::now();
            let pk = Groth16Keys::read_proving_key(&pk_path).with_context(|| {
                format!(
                    "reading proving key {} (run `xark setup` first?)",
                    pk_path.display()
                )
            });
            if timing {
                eprintln!("PROVE_TIME:   [key]     load={:?}", tk.elapsed());
            }
            pk
        },
        || -> anyhow::Result<_> {
            if args.r1cs.is_none() && args.circuit.is_none() && xbc.exists() {
                let tr = std::time::Instant::now();
                let bytes =
                    std::fs::read(&xbc).with_context(|| format!("reading {}", xbc.display()))?;
                let fingerprint = super::sha256_hex(&bytes);
                let t_read = tr.elapsed();
                let te = std::time::Instant::now();
                // Reduced (per-template minimized) R1CS is the default; the flat/off
                // modes use the full expand for the proof's R1CS too.
                let template_min =
                    !super::dbg_flag("XARK_FLAT_MINIMIZE") && !super::dbg_flag("XARK_NO_MINIMIZE");
                // Full circuit — used to SOLVE the witness (all vars computed).
                let cp = xark_ir::function_decode::expand_function_blob(&bytes)
                    .map_err(|e| anyhow::anyhow!(e))?;
                let t_expand = te.elapsed();
                let id_inputs = resolve_input_ids(&cp.vars, &inputs)?;
                let ts = std::time::Instant::now();
                let assign_fp = soundness_check(&cp, profile.as_ref(), &id_inputs)?;
                let t_solve = ts.elapsed();
                let ti = std::time::Instant::now();
                // Groth16 R1CS view — the reduced (per-template minimized) circuit,
                // matching what `xark setup` keyed the proving key to. Prefer the
                // setup cache (a fingerprint-matched minimized R1CS): loading it
                // skips the reduced-expand + boundary-minimize + `validate()`
                // entirely, and the load is hidden under the concurrent pk read.
                // Fall back to recomputing if the cache is absent or stale.
                let (prog, preminimized) = if template_min {
                    match try_load_r1cs_cache(&cache_path, &fingerprint) {
                        Some(cached) => (cached, true),
                        None => (
                            xark_ir::function_decode::expand_function_blob_reduced(&bytes)
                                .map_err(|e| anyhow::anyhow!(e))?
                                .into_r1cs(),
                            false,
                        ),
                    }
                } else {
                    (cp.into_r1cs(), false)
                };
                if timing {
                    eprintln!(
                        "PROVE_TIME:   [circuit] read+hash={t_read:?} expand={t_expand:?} \
                         solve+soundness={t_solve:?} into_r1cs/cache={:?} cached={preminimized}",
                        ti.elapsed()
                    );
                }
                Ok((prog, assign_fp, fingerprint, preminimized))
            } else {
                let (prog, fp) = load_backend_r1cs(&xbc, args.r1cs.as_deref(), &r1cs_path)?;
                let prim = load_circuit_auto(&circuit_path)?;
                let id_inputs = resolve_input_ids(&prim.vars, &inputs)?;
                let assign_fp = soundness_check_r1cs(&prim, &prog, profile.as_ref(), &id_inputs)?;
                Ok((prog, assign_fp, fp, false))
            }
        },
    );
    let pk = pk_res?;
    let (prog, assign_fp, circuit_fingerprint, preminimized) = circuit_res?;
    let t_load_solve = t_conc.elapsed();

    let t_conv = std::time::Instant::now();
    let assign: BTreeMap<VarId, ark_bn254::Fr> = assign_fp
        .iter()
        .map(|(k, v)| {
            // BN254 witness values come straight out of the solver as `Fr`; only
            // the (unprovable-anyway) non-BN254 fallback needs a decimal reparse.
            (
                *k,
                v.as_bn254_fr()
                    .unwrap_or_else(|| fr_from_decimal(&v.to_decimal())),
            )
        })
        .collect();
    if timing {
        eprintln!("PROVE_TIME: witness->Fr = {:?}", t_conv.elapsed());
    }
    let n_constraints = prog.constraints.len();
    let t_build = std::time::Instant::now();
    // A cache hit gives the already-minimized circuit `xark setup` keyed to, so
    // skip re-minimizing; otherwise minimize (matching setup) in `for_proving`.
    let circuit = if preminimized {
        XarkCircuit::for_proving_preminimized(prog, assign)
    } else {
        XarkCircuit::for_proving(prog, assign)
    };
    // Reject a malformed `r1cs.json` before synthesis (clean error, not a panic).
    // The cached circuit was already validated at setup, so skip the re-validate.
    if !preminimized {
        circuit
            .validate()
            .map_err(|e| anyhow::anyhow!("malformed circuit: {e}"))?;
    }
    let public = circuit.public_inputs();
    if timing {
        eprintln!(
            "PROVE_TIME: circuit build+validate = {:?}",
            t_build.elapsed()
        );
    }

    // `--cache` warm-on-miss: we just derived the minimized circuit the hard way,
    // so persist it (tagged with this circuit's fingerprint) for the next prove.
    // A hit (`preminimized`) needs no write — it came from the cache already.
    if args.cache && !preminimized {
        match xark_ir::r1cs_cache::serialize(&circuit_fingerprint, circuit.prog()) {
            Ok(bytes) => match std::fs::write(&cache_path, &bytes) {
                Ok(()) if timing => {
                    eprintln!("PROVE_TIME: warmed r1cs cache = {} bytes", bytes.len())
                }
                Ok(()) => {}
                Err(e) => eprintln!(
                    "warning: could not write R1CS cache {}: {e}",
                    cache_path.display()
                ),
            },
            Err(e) => eprintln!("warning: could not encode R1CS cache: {e}"),
        }
    }

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
    let t_prove_start = std::time::Instant::now();
    let proof = prove(&pk, circuit, &public, &mut rng).map_err(synth_err)?;
    if timing {
        eprintln!(
            "PROVE_TIME: load+solve+key (concurrent) = {:?}  groth16-prove = {:?}  \
             ({} constraints)",
            t_load_solve,
            t_prove_start.elapsed(),
            n_constraints,
        );
    }

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
    let name = project.entry_name();
    let bundle_json = serde_json::json!({
        "circuit": name,
        "circuit_hash": format!("sha256:{circuit_fingerprint}"),
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
    // "Built" is signalled by `circuit.xbc` (always emitted), not `r1cs.json`
    // (now `--emit-json`-only): a normal build no longer writes the JSON.
    let is_built = project.circuit_xbc().exists() || r1cs_path.exists();
    if args.r1cs.is_none()
        && !is_built
        && let Some(dir) = find_crate_dir(args, project)
    {
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
            r1cs: args.r1cs.clone(),
            out: None,
            insecure_dev_mode: true,
            deterministic_rng: None,
            ptau_file: None,
            phase2_seed: None,
            // Always cache here: this auto-setup exists only to feed the prove that
            // immediately follows in the same process, and that prove reads the
            // cache (fingerprint-gated). Without it, setup and prove would each run
            // the (expensive) boundary minimize on the identical circuit — the whole
            // point of the cache. Independent of the user's `--cache` (which governs
            // whether a *standalone* `xark setup` persists it for later proofs).
            cache: true,
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
