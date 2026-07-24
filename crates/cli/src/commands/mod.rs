//! The clap-driven `xark` CLI.
//!
//! Frontend subcommands (`init`/`build`/`check`) drive `cargo` with `xark` as
//! `RUSTC`; their implementations live in [`crate::cli`]. Backend subcommands
//! (`setup`/`prove`/`verify`/`export`/`ceremony`/`inspect`) read the xark-IR
//! produced by `xark build` and run the shared Arkworks Groth16 backend.

use std::collections::BTreeMap;

use anyhow::{Context, Result};
use ark_bn254::Fr;
use clap::{Parser, Subcommand};
use tracing_subscriber::EnvFilter;

use xark_ir::primitive::{PrimitiveProgram, VarRole};
use xark_ir::profile::ProfileProgram;
use xark_ir::solver::Fp;
use xark_ir::{R1csProgram, VarId, Visibility};

/// Developer-diagnostics env-flag probe. Only reads the environment under the
/// `debug` feature; a normal build compiles it to `false`, so the diagnostic
/// branches and their `XARK_*` knobs vanish.
#[inline]
pub(crate) fn dbg_flag(name: &str) -> bool {
    #[cfg(feature = "debug")]
    {
        std::env::var(name).is_ok()
    }
    #[cfg(not(feature = "debug"))]
    {
        let _ = name;
        false
    }
}

pub mod ceremony;
pub mod check;
pub mod client;
pub mod completions;
pub mod doctor;
pub mod export;
pub mod inspect;
pub mod profile;
pub mod prove;
pub mod setup;
pub mod verify;

/// Wrap an Arkworks `gr1cs` `SynthesisError` (or any backend error) into an
/// `anyhow::Error`. The ark error types are `no_std` and don't implement
/// `std::error::Error`, so we wrap via their `Display` impl.
pub fn synth_err<E: std::fmt::Display>(e: E) -> anyhow::Error {
    anyhow::anyhow!("R1CS synthesis error: {e}")
}

/// `xark` — write, compile, prove and verify zero-knowledge circuits in Rust.
#[derive(Parser, Debug)]
#[command(
    name = "xark",
    version = concat!(env!("CARGO_PKG_VERSION"), " (", env!("XARK_GIT_HASH"), ")"),
    styles = crate::style::clap_styles(),
    about = "Write, compile, prove and verify zero-knowledge circuits in Rust",
    long_about = "xark compiles a restricted Rust circuit (via rustc MIR) into \
xark-IR + R1CS, then proves and verifies it with an Arkworks Groth16 backend \
over BN254. `xark build` emits `circuit.json` + `r1cs.json` under \
`<crate>/target/xark/`; the backend commands read them from there \
automatically."
)]
pub struct Cli {
    #[command(subcommand)]
    pub command: Command,
}

#[derive(Subcommand, Debug)]
pub enum Command {
    /// Check your toolchain is set up to build & prove circuits.
    Doctor(doctor::DoctorArgs),
    /// Scaffold a starter circuit crate (rust-analyzer ready).
    #[command(alias = "new")]
    Init(InitArgs),
    /// Compile a circuit crate (rustc-MIR → xark-IR → R1CS) into target/xark/.
    Build(BuildArgs),
    /// Validate a circuit crate and report subset rejections as diagnostics.
    Check(CheckArgs),
    /// Build the circuit, then run its `cargo test` circuit tests.
    Test(TestArgs),
    /// Remove all xark build output (every `target/xark/` under the current dir).
    Clean(CleanArgs),
    /// Generate Groth16 proving and verifying keys.
    Setup(setup::SetupArgs),
    /// Solve the witness from --inputs values and produce a Groth16 proof.
    Prove(prove::ProveArgs),
    /// Verify a Groth16 proof against public inputs.
    Verify(verify::VerifyArgs),
    /// Export a self-contained Solana verifier crate.
    Export(export::ExportArgs),
    /// Scaffold a TypeScript client (verify with snarkjs + on-chain calldata).
    Client(client::ClientArgs),
    /// Phase-2 MPC ceremony for trusted setup.
    Ceremony(ceremony::CeremonyArgs),
    /// Print circuit statistics (variables, constraints, public inputs).
    Inspect(inspect::InspectArgs),
    /// Profile a circuit: attribute each constraint to its source line, function
    /// chain, and kind, then print a sorted drill-down.
    Profile(profile::ProfileArgs),
    /// Generate shell completion scripts.
    Completions(completions::CompletionsArgs),
}

/// Entry point invoked from `crate::main` once a CLI subcommand is detected.
pub fn main() {
    let filter = EnvFilter::try_from_default_env().unwrap_or_else(|_| EnvFilter::new("info"));
    tracing_subscriber::fmt()
        .with_env_filter(filter)
        .with_target(false)
        .with_writer(std::io::stderr)
        .init();

    let cli = Cli::parse();
    let code = match run(cli) {
        Ok(()) => 0,
        Err(e) => {
            eprintln!("{} {e:#}", crate::style::err("error:"));
            1
        }
    };
    std::process::exit(code);
}

fn run(cli: Cli) -> Result<()> {
    match cli.command {
        Command::Doctor(a) => doctor::run(a),
        // Frontend commands delegate to the hand-rolled `cargo`-driving
        // implementations, which return a process exit code.
        Command::Init(a) => exit_code("init", crate::cli::cmd_init(&a.to_argv())),
        Command::Build(a) => exit_code("build", crate::cli::cmd_build(&a.to_argv())),
        // Bare `xark check` stays the fast, artifact-free `cargo check` validator.
        // `xark check --inputs …` opts into the witness-based soundness analyzer
        // (build + solve + `analyze_underconstrained`), which is `anyhow`-based.
        Command::Check(a) if a.inputs.is_none() => {
            exit_code("check", crate::cli::cmd_check(&a.to_argv()))
        }
        Command::Check(a) => check::run(a),
        Command::Test(a) => exit_code("test", crate::cli::cmd_test(&a.to_argv())),
        Command::Clean(a) => exit_code("clean", crate::cli::cmd_clean(&a.to_argv())),
        // Backend commands are `anyhow`-based.
        Command::Setup(a) => setup::run(a),
        Command::Prove(a) => prove::run(a),
        Command::Verify(a) => verify::run(a),
        Command::Export(a) => export::run(a),
        Command::Client(a) => client::run(a),
        Command::Ceremony(a) => ceremony::run(a),
        Command::Inspect(a) => inspect::run(a),
        Command::Profile(a) => profile::run(a),
        Command::Completions(a) => completions::run(a),
    }
}

/// Bridge a frontend command's process exit code into the `anyhow` flow: exit
/// straight away on failure (the frontend already printed a diagnostic).
fn exit_code(_name: &str, code: i32) -> Result<()> {
    if code == 0 {
        Ok(())
    } else {
        std::process::exit(code);
    }
}

// Frontend argument structs (delegate to `crate::cli`).

#[derive(clap::Args, Debug)]
pub struct InitArgs {
    /// Name of the crate to scaffold. Omit to initialize the current directory.
    pub name: Option<String>,
}

impl InitArgs {
    fn to_argv(&self) -> Vec<String> {
        self.name.iter().cloned().collect()
    }
}

#[derive(clap::Args, Debug)]
pub struct BuildArgs {
    /// Circuit crate directory to build.
    #[arg(default_value = ".", value_hint = clap::ValueHint::DirPath)]
    pub crate_dir: String,
    /// Output directory for `circuit.json` / `r1cs.json`
    /// (default: `<crate>/target/xark/`).
    #[arg(long, value_hint = clap::ValueHint::DirPath)]
    pub out: Option<String>,
    /// Field the circuit is defined over.
    #[arg(long, default_value = "bn254")]
    pub field: String,
    /// Also emit the human-readable `circuit.json` (the primitive program as
    /// JSON). Off by default: `xark prove`/`check` load the compact binary
    /// `circuit.xbc` instead, so a normal build skips the (multi-GB on large
    /// circuits) JSON serialization. `r1cs.json` is always written.
    #[arg(long = "emit-json", default_value_t = false)]
    pub emit_json: bool,
}

impl BuildArgs {
    fn to_argv(&self) -> Vec<String> {
        let mut v = vec![self.crate_dir.clone()];
        if let Some(out) = &self.out {
            v.push("--out".into());
            v.push(out.clone());
        }
        v.push("--field".into());
        v.push(self.field.clone());
        if self.emit_json {
            v.push("--emit-json".into());
        }
        v
    }
}

#[derive(clap::Args, Debug)]
pub struct CleanArgs {}

impl CleanArgs {
    fn to_argv(&self) -> Vec<String> {
        Vec::new()
    }
}

#[derive(clap::Args, Debug)]
pub struct CheckArgs {
    /// Circuit crate directory to validate.
    #[arg(default_value = ".", value_hint = clap::ValueHint::DirPath)]
    pub crate_dir: String,
    /// Emit machine-readable JSON diagnostics (for editors / rust-analyzer).
    #[arg(long = "message-format", value_parser = ["json", "human"])]
    pub message_format: Option<String>,
    /// Also write per-line constraint-cost attribution to
    /// `target/xark/<pkg>/profile.json` (and a `metadata.json` with circuit
    /// stats). Consumed by editor extensions and `xark profile`.
    #[arg(long, default_value_t = false)]
    pub profile: bool,
    /// Circuit inputs as inline JSON `{"name": value, …}` or a path to an input
    /// file. Passing `--inputs` opts into the witness-based under-constrained
    /// soundness check: xark builds the circuit, solves the witness from these
    /// inputs, and reports any derived variable the constraints fail to pin.
    /// Provide every circuit input, as `xark prove` does. With no `--inputs`,
    /// `check` stays the fast validator.
    #[arg(long = "inputs", value_name = "JSON|FILE")]
    pub inputs: Option<String>,
    /// Output directory for the intermediate `circuit.json` / `r1cs.json` built
    /// by `--inputs` (default: `<crate>/target/xark/`). Only used with `--inputs`.
    #[arg(long, value_hint = clap::ValueHint::DirPath)]
    pub out: Option<String>,
}

impl CheckArgs {
    fn to_argv(&self) -> Vec<String> {
        let mut v = vec![self.crate_dir.clone()];
        if self.message_format.as_deref() == Some("json") {
            v.push("--message-format=json".into());
        }
        if self.profile {
            v.push("--profile".into());
        }
        v
    }
}

#[derive(clap::Args, Debug)]
pub struct TestArgs {
    /// Circuit crate directory to build and test.
    #[arg(default_value = ".", value_hint = clap::ValueHint::DirPath)]
    pub crate_dir: String,
    /// Extra arguments forwarded verbatim to `cargo test` (after `--`).
    #[arg(last = true)]
    pub cargo_args: Vec<String>,
}

impl TestArgs {
    fn to_argv(&self) -> Vec<String> {
        let mut v = vec![self.crate_dir.clone()];
        if !self.cargo_args.is_empty() {
            v.push("--".into());
            v.extend(self.cargo_args.iter().cloned());
        }
        v
    }
}

// Shared helpers for the backend commands.

/// Render the path argument the user passed (for the guided "Next:" hints) so
/// suggested commands are copy-pasteable. Falls back to `.` when none was given.
pub fn path_arg(path: &Option<std::path::PathBuf>) -> String {
    match path {
        Some(p) => p.display().to_string(),
        None => ".".to_string(),
    }
}

/// Parse the `--inputs` argument: a leading `{` selects inline JSON, anything
/// else is a file path (JSON object, or `name = value` lines). Array elements
/// use the flat names `xark inspect` prints, e.g. `path[0]`.
pub fn parse_inputs_arg(arg: &str) -> Result<BTreeMap<String, String>> {
    if arg.trim_start().starts_with('{') {
        parse_input_text(arg, std::path::Path::new("<--inputs>"))
    } else {
        let text = std::fs::read_to_string(arg)
            .with_context(|| format!("reading --inputs file `{arg}`"))?;
        parse_input_text(&text, std::path::Path::new(arg))
    }
}

/// Parse input text: either a `{ "name": value, … }` JSON object, or lines of
/// `name = value` (`#` comments and blank lines ignored). Values are kept as
/// decimal strings; array elements use the flat names `xark inspect` prints.
pub fn parse_input_text(text: &str, source: &std::path::Path) -> Result<BTreeMap<String, String>> {
    let mut out = BTreeMap::new();

    if text.trim_start().starts_with('{') {
        let obj: serde_json::Value = serde_json::from_str(text)
            .with_context(|| format!("parsing {} as JSON", source.display()))?;
        let map = obj.as_object().ok_or_else(|| {
            anyhow::anyhow!("{}: expected a JSON object of name→value", source.display())
        })?;
        for (name, value) in map {
            let v = match value {
                serde_json::Value::String(s) => s.clone(),
                serde_json::Value::Number(n) => n.to_string(),
                other => anyhow::bail!(
                    "{}: input `{name}` must be a decimal string or number, got {other}",
                    source.display()
                ),
            };
            out.insert(name.clone(), v);
        }
        return Ok(out);
    }

    for (lineno, raw) in text.lines().enumerate() {
        let line = raw.split('#').next().unwrap_or("").trim();
        if line.is_empty() {
            continue;
        }
        let (name, value) = line.split_once('=').with_context(|| {
            format!(
                "{}:{}: expected `name = value`",
                source.display(),
                lineno + 1
            )
        })?;
        let value = value.trim().trim_matches('"').trim_matches('\'');
        out.insert(name.trim().to_string(), value.to_string());
    }
    Ok(out)
}

/// Render a copy-pasteable `--inputs` JSON template naming every declared input,
/// e.g. `--inputs '{"secret": <value>, "result": <value>}'`.
pub fn inputs_hint(names: &[&str]) -> String {
    let body = names
        .iter()
        .map(|n| format!("\"{n}\": <value>"))
        .collect::<Vec<_>>()
        .join(", ");
    format!("--inputs '{{{body}}}'")
}

/// Load and parse an `r1cs.json` file.
pub fn load_r1cs(path: &std::path::Path) -> Result<R1csProgram> {
    let s = std::fs::read_to_string(path)
        .with_context(|| format!("reading {} (run `xark build` first?)", path.display()))?;
    xark_ir::json::from_json(&s).with_context(|| format!("parsing {}", path.display()))
}

/// Load and parse a `circuit.json` (primitive / witness-gen) file.
pub fn load_circuit(path: &std::path::Path) -> Result<PrimitiveProgram> {
    let s = std::fs::read_to_string(path)
        .with_context(|| format!("reading {} (run `xark build` first?)", path.display()))?;
    xark_ir::primitive::from_json(&s).with_context(|| format!("parsing {}", path.display()))
}

/// True if `bytes` is a current `XBC` version-1 circuit container. The magic +
/// u16 version guard rejects stale/foreign files so every loader can dispatch on
/// it (version 1 is the only format).
pub fn is_function_artifact(bytes: &[u8]) -> bool {
    bytes.len() >= 6 && bytes[0..4] == *b"XBC\0" && u16::from_le_bytes([bytes[4], bytes[5]]) == 1
}

pub fn load_circuit_program(path: &std::path::Path) -> Result<xark_ir::CircuitProgram> {
    let bytes = std::fs::read(path)
        .with_context(|| format!("reading {} (run `xark build` first?)", path.display()))?;
    if !is_function_artifact(&bytes) {
        anyhow::bail!(
            "{} is not a current circuit artifact — rebuild with `xark build`",
            path.display()
        );
    }
    xark_ir::function_decode::expand_function_blob(&bytes).map_err(|e| anyhow::anyhow!(e))
}

/// Load the Groth16 backend's [`R1csProgram`] from a built circuit, preferring
/// the self-contained `circuit.xbc` (deriving the R1CS from it) and falling back
/// to `r1cs.json` — either an explicit `--r1cs <path>` override or an
/// `--emit-json` / legacy build. Also returns the SHA-256 fingerprint of the
/// bytes it read, used to stamp the proof bundle's `circuit_hash`.
pub fn load_backend_r1cs(
    xbc_path: &std::path::Path,
    r1cs_override: Option<&std::path::Path>,
    r1cs_default: &std::path::Path,
) -> Result<(R1csProgram, String)> {
    if let Some(p) = r1cs_override {
        let s = std::fs::read_to_string(p)
            .with_context(|| format!("reading {} (run `xark build` first?)", p.display()))?;
        let prog =
            xark_ir::json::from_json(&s).with_context(|| format!("parsing {}", p.display()))?;
        return Ok((prog, sha256_hex(s.as_bytes())));
    }
    if xbc_path.exists() {
        let bytes =
            std::fs::read(xbc_path).with_context(|| format!("reading {}", xbc_path.display()))?;
        let fingerprint = sha256_hex(&bytes);
        if !is_function_artifact(&bytes) {
            anyhow::bail!(
                "{} is not a current circuit artifact — rebuild with `xark build`",
                xbc_path.display()
            );
        }
        // Groth16 view. By default expand the reduced R1CS (each template
        // minimized once), avoiding the full flat expansion + flat minimize.
        // `XARK_FLAT_MINIMIZE` / `XARK_NO_MINIMIZE` fall back to the full expand.
        let use_reduced = !dbg_flag("XARK_FLAT_MINIMIZE") && !dbg_flag("XARK_NO_MINIMIZE");
        let cp = if use_reduced {
            xark_ir::function_decode::expand_function_blob_reduced(&bytes)
        } else {
            xark_ir::function_decode::expand_function_blob(&bytes)
        }
        .map_err(|e| anyhow::anyhow!(e))?;
        return Ok((cp.into_r1cs(), fingerprint));
    }
    let s = std::fs::read_to_string(r1cs_default).with_context(|| {
        format!(
            "reading {} (run `xark build` first?)",
            r1cs_default.display()
        )
    })?;
    let prog = xark_ir::json::from_json(&s)
        .with_context(|| format!("parsing {}", r1cs_default.display()))?;
    Ok((prog, sha256_hex(s.as_bytes())))
}

/// Load the solver-facing [`PrimitiveProgram`] from a `circuit.xbc`.
pub fn load_circuit_xbc_parallel(path: &std::path::Path) -> Result<PrimitiveProgram> {
    load_circuit_program(path).map(|cp| cp.to_primitive())
}

/// Load a [`PrimitiveProgram`] from either the binary `circuit.xbc` (default,
/// via the parallel bytecode expander) or a `circuit.json` — dispatched on the
/// path's extension. `xark build` always writes `circuit.xbc` and only writes
/// `circuit.json` under `--emit-json`, so the default backend path resolves to
/// the `.xbc`; an explicit `--circuit foo.json` still works.
pub fn load_circuit_auto(path: &std::path::Path) -> Result<PrimitiveProgram> {
    if path.extension().is_some_and(|e| e == "xbc") {
        load_circuit_xbc_parallel(path)
    } else {
        load_circuit(path)
    }
}

/// Best-effort load of `profile.json` (per-constraint source/function attribution)
/// from a build directory, for richer failure diagnostics. Returns `None` when
/// the circuit was built without `--profile` (or the file is malformed).
pub fn load_profile(dir: &std::path::Path) -> Option<ProfileProgram> {
    std::fs::read_to_string(dir.join("profile.json"))
        .ok()
        .and_then(|s| xark_ir::profile::from_json(&s).ok())
}

/// A `0x`-prefixed hex string → raw bytes (rejects a missing prefix / odd length).
fn parse_hex_bytes(s: &str) -> Result<Vec<u8>> {
    let h = s
        .strip_prefix("0x")
        .or_else(|| s.strip_prefix("0X"))
        .ok_or_else(|| anyhow::anyhow!("expected a 0x-prefixed hex string, got `{s}`"))?;
    hex::decode(h).map_err(|e| anyhow::anyhow!("invalid hex `{s}`: {e}"))
}

/// A 256-bit input value → big-endian bytes: a `0x`-hex string (the natural form
/// of a crypto scalar/coordinate) or a plain decimal.
fn value_to_be_bytes(v: &str) -> Result<Vec<u8>> {
    if v.starts_with("0x") || v.starts_with("0X") {
        parse_hex_bytes(v)
    } else {
        num_bigint::BigUint::parse_bytes(v.trim().as_bytes(), 10)
            .map(|n| n.to_bytes_be())
            .ok_or_else(|| anyhow::anyhow!("expected a decimal or `0x`-hex value, got `{v}`"))
    }
}

/// The limb bit-width for an `N`-limb non-native value: 2×128 (the packed secp
/// half form) or 3×86 (the default field-element layout).
fn limb_bits(n_limbs: usize) -> Result<u32> {
    match n_limbs {
        2 => Ok(128),
        3 => Ok(86),
        n => anyhow::bail!("unsupported {n}-limb layout (expected 2×128 or 3×86)"),
    }
}

/// Count the `prefix.limbs[i]` leaves present in `vars` (`0` if none).
fn count_limbs(vars: &[xark_ir::primitive::Var], prefix: &str) -> usize {
    let key = format!("{prefix}.limbs");
    vars.iter()
        .filter(|v| array_index(&v.name, &key).is_some())
        .count()
}

/// The distinct `<field>` names of a compound input `prefix.<field>.limbs[i]`
/// (e.g. `["x", "y"]` for a point, `["r", "s"]` for a signature), name-sorted.
fn sub_fields(vars: &[xark_ir::primitive::Var], prefix: &str) -> Vec<String> {
    let pre = format!("{prefix}.");
    let mut fs: Vec<String> = vars
        .iter()
        .filter_map(|v| {
            let (f, tail) = v.name.strip_prefix(&pre)?.split_once('.')?;
            tail.starts_with("limbs[").then(|| f.to_string())
        })
        .collect();
    fs.sort_unstable();
    fs.dedup();
    fs
}

/// A byte-array leaf `name[i]` → its index `i` (only a flat 1-D index; nested /
/// multi-dim names like `x.bits[0][1]` return `None`).
fn array_index(leaf: &str, name: &str) -> Option<usize> {
    let inner = leaf
        .strip_prefix(name)?
        .strip_prefix('[')?
        .strip_suffix(']')?;
    if inner.contains('[') {
        return None;
    }
    inner.parse().ok()
}

/// A SHA-256 digest leaf `name.bits[w][j]` → `(word, bit)`.
fn digest_index(leaf: &str, name: &str) -> Option<(usize, usize)> {
    let rest = leaf.strip_prefix(name)?.strip_prefix(".bits[")?;
    let (w, rest) = rest.split_once("][")?;
    let j = rest.strip_suffix(']')?;
    Some((w.parse().ok()?, j.parse().ok()?))
}

/// The logical input a leaf belongs to (`input[3]` → `input`, `d.bits[0][1]` → `d`).
fn logical_root(leaf: &str) -> &str {
    let cut = leaf.find(['[', '.']).unwrap_or(leaf.len());
    &leaf[..cut]
}

/// Resolve `name → value` inputs to `VarId → decimal` for the solver.
///
/// Shared by `xark prove` and `xark check --inputs`. A name may be a single leaf
/// or a **logical input** that fans out to its leaves:
///   * scalar `Field` → decimal, or `0x`-hex (reduced mod p);
///   * byte array `[u8; N]` (leaves `name[i]`) → a `0x`-hex string of exactly `N`
///     bytes, one byte per leaf;
///   * hash (leaves `name.hi` / `name.lo`) → a `0x`-hex string of 32 bytes packed
///     into two 128-bit field halves (top 16 bytes → `hi`, low 16 → `lo`);
///   * SHA-256 digest (leaves `name.bits[w][j]`) → a `0x`-hex string of 32 bytes,
///     decomposed into the 256 bit leaves in the gadget's word/byte/bit layout.
///
/// A wrong value can only yield an unsatisfiable witness (a clear failure), never
/// a false proof, so this stays a convenience over the always-safe flat form.
pub fn resolve_input_ids(
    vars: &[xark_ir::primitive::Var],
    inputs: &BTreeMap<String, String>,
) -> Result<BTreeMap<VarId, String>> {
    let by_name: BTreeMap<&str, VarId> = vars.iter().map(|v| (v.name.as_str(), v.id)).collect();
    let is_hex = |s: &str| s.starts_with("0x") || s.starts_with("0X");
    let mut id_inputs: BTreeMap<VarId, String> = BTreeMap::new();

    for (k, v) in inputs {
        // 1. Exact leaf — a scalar value (decimal, or `0x`-hex reduced mod p).
        if let Some(&id) = by_name.get(k.as_str()) {
            let dec = if is_hex(v) {
                xark_prover::hex_to_field_decimal(v)
                    .map_err(|e| anyhow::anyhow!("input `{k}`: {e}"))?
            } else {
                xark_prover::try_fr_from_decimal(v)
                    .map_err(|e| anyhow::anyhow!("invalid value for input `{k}`: {e}"))?;
                v.clone()
            };
            id_inputs.insert(id, dec);
            continue;
        }

        // 2. Byte array `name[i]` — a `0x`-hex string, one byte per leaf.
        let mut arr: Vec<(usize, VarId)> = vars
            .iter()
            .filter_map(|var| array_index(&var.name, k).map(|i| (i, var.id)))
            .collect();
        if !arr.is_empty() {
            arr.sort_unstable_by_key(|(i, _)| *i);
            let bytes = parse_hex_bytes(v).map_err(|e| anyhow::anyhow!("input `{k}`: {e}"))?;
            if bytes.len() != arr.len() {
                anyhow::bail!(
                    "input `{k}` is a {}-byte array, but the hex value has {} bytes",
                    arr.len(),
                    bytes.len()
                );
            }
            for ((_, id), byte) in arr.iter().zip(bytes) {
                id_inputs.insert(*id, byte.to_string());
            }
            continue;
        }

        // 3. Packed hash `name.hi` / `name.lo` — a 32-byte `0x`-hex value split into
        //    two 128-bit field halves (top 16 bytes → hi, low 16 → lo, big-endian).
        if let (Some(&hi_id), Some(&lo_id)) = (
            by_name.get(format!("{k}.hi").as_str()),
            by_name.get(format!("{k}.lo").as_str()),
        ) {
            let bytes = parse_hex_bytes(v).map_err(|e| anyhow::anyhow!("input `{k}`: {e}"))?;
            if bytes.len() != 32 {
                anyhow::bail!(
                    "hash input `{k}` needs a 32-byte hex value, but got {} bytes",
                    bytes.len()
                );
            }
            let pack = |chunk: &[u8]| chunk.iter().fold(0u128, |acc, &b| (acc << 8) | b as u128);
            id_inputs.insert(hi_id, pack(&bytes[..16]).to_string());
            id_inputs.insert(lo_id, pack(&bytes[16..]).to_string());
            continue;
        }

        // 4. SHA-256 digest `name.bits[w][j]` — a 32-byte `0x`-hex hash. Byte `idx`
        //    occupies word `idx/4`, big-endian slot within the word; leaf bit `j`
        //    of word `w` is bit `j%8` of hash byte `4w + (3 - j/8)`.
        let dig: Vec<((usize, usize), VarId)> = vars
            .iter()
            .filter_map(|var| digest_index(&var.name, k).map(|wj| (wj, var.id)))
            .collect();
        if !dig.is_empty() {
            let bytes = parse_hex_bytes(v).map_err(|e| anyhow::anyhow!("input `{k}`: {e}"))?;
            if bytes.len() != 32 {
                anyhow::bail!(
                    "digest input `{k}` needs a 32-byte hex value, but got {} bytes",
                    bytes.len()
                );
            }
            for ((w, j), id) in dig {
                let byte = bytes[4 * w + (3 - j / 8)];
                id_inputs.insert(id, ((byte >> (j % 8)) & 1).to_string());
            }
            continue;
        }

        // 5. Non-native scalar `name.limbs[i]` — a 256-bit value (a `0x`-hex crypto
        //    scalar or a decimal) fanned out to its `N` little-endian limbs via the
        //    same `limb_leaves` the gadget's host `NativeInput` uses. `N` picks the
        //    layout: 2 → 128-bit halves (packed secp), 3 → 86-bit limbs.
        let n_scalar = count_limbs(vars, k);
        if n_scalar > 0 {
            let be = value_to_be_bytes(v).map_err(|e| anyhow::anyhow!("input `{k}`: {e}"))?;
            let bits = limb_bits(n_scalar)?;
            for (name, dec) in xark_prover::limb_leaves(&be, k, n_scalar, bits) {
                if let Some(&id) = by_name.get(name.as_str()) {
                    id_inputs.insert(id, dec);
                }
            }
            continue;
        }

        // 6. Non-native compound `name.<field>.limbs[i]` (an affine point `x ‖ y`,
        //    an ECDSA signature `r ‖ s`, …) — a big-endian concatenation of its
        //    32-byte fields (with an optional SEC1 `0x04` tag), each field fanned
        //    out like case 5. Fields are taken in name order (`r`<`s`, `x`<`y`),
        //    matching the wire concatenation.
        let fields = sub_fields(vars, k);
        if !fields.is_empty() {
            let mut bytes = parse_hex_bytes(v).map_err(|e| anyhow::anyhow!("input `{k}`: {e}"))?;
            let want = fields.len() * 32;
            if bytes.len() == want + 1 && bytes[0] == 0x04 {
                bytes.remove(0); // strip the SEC1 uncompressed-point tag
            }
            if bytes.len() != want {
                anyhow::bail!(
                    "compound input `{k}` ({} fields: {fields:?}) needs a {want}-byte \
                     big-endian value{}, but got {} bytes",
                    fields.len(),
                    if fields.len() == 2 {
                        " (or 65 with the 0x04 SEC1 tag)"
                    } else {
                        ""
                    },
                    bytes.len()
                );
            }
            for (i, f) in fields.iter().enumerate() {
                let chunk = &bytes[i * 32..(i + 1) * 32];
                let n = count_limbs(vars, &format!("{k}.{f}"));
                for (name, dec) in
                    xark_prover::limb_leaves(chunk, &format!("{k}.{f}"), n, limb_bits(n)?)
                {
                    if let Some(&id) = by_name.get(name.as_str()) {
                        id_inputs.insert(id, dec);
                    }
                }
            }
            continue;
        }

        // Unknown — list the circuit's logical inputs (deduped roots, not leaves).
        let mut roots: Vec<&str> = vars
            .iter()
            .filter(|v| !matches!(v.role, VarRole::Derived))
            .map(|v| logical_root(&v.name))
            .collect();
        roots.sort_unstable();
        roots.dedup();
        anyhow::bail!("unknown input `{k}` (circuit inputs: {roots:?})");
    }
    Ok(id_inputs)
}

/// The witness-based under-constrained soundness gate, shared by `xark prove`
/// and `xark check --inputs`.
///
/// Solves the witness from `id_inputs`, then runs
/// [`xark_ir::solver::analyze_underconstrained`]: if any derived variable is not
/// uniquely pinned by the constraints (a value a malicious prover could forge
/// without violating any constraint — a genuine soundness hole), it `bail!`s
/// listing each hole. On success it returns the solved assignment.
///
/// Witness-based: it needs the solved assignment, so it runs after solving and
/// before key-loading / synthesis. A structural, witness-free version at
/// `xark build`/`check` is planned.
pub fn soundness_check(
    cp: &xark_ir::CircuitProgram,
    profile: Option<&ProfileProgram>,
    id_inputs: &BTreeMap<VarId, String>,
) -> Result<BTreeMap<VarId, Fp>> {
    // Solve + check directly on the R1CS rows (no `to_primitive` flattening). On
    // an unsatisfied witness, name *which* constraint (and, when profiled, its
    // source line / function) failed — the same explanation `xark test` surfaces;
    // the R1CS is materialized only here, on the (rare) error path.
    let describe = |e| {
        let r1cs = cp.to_r1cs();
        anyhow::anyhow!(
            "{}",
            xark_ir::diagnose::describe_unsatisfied(&e, &r1cs, profile)
        )
    };
    let timing = dbg_flag("PROVE_TIME");
    let t = std::time::Instant::now();
    let assign_fp = xark_ir::solver::solve_cp(cp, id_inputs).map_err(describe)?;
    let t_solve = t.elapsed();
    let t = std::time::Instant::now();
    xark_ir::solver::check_cp(cp, &assign_fp).map_err(describe)?;
    let t_check = t.elapsed();
    let t = std::time::Instant::now();
    let holes = xark_ir::solver::analyze_underconstrained_cp(cp, &assign_fp);
    if timing {
        eprintln!(
            "PROVE_TIME:   solve={:?}  check={:?}  analyze={:?}",
            t_solve,
            t_check,
            t.elapsed()
        );
    }
    report_underconstrained(holes)?;
    Ok(assign_fp)
}

/// The `--r1cs`/`--circuit` override path of `xark prove`: the same gate over a
/// `PrimitiveProgram` (Expression) + `R1csProgram` loaded from JSON, rather than
/// a `circuit.xbc`. The default path uses [`soundness_check`] on the
/// `CircuitProgram` directly.
pub fn soundness_check_r1cs(
    prim: &PrimitiveProgram,
    r1cs: &R1csProgram,
    profile: Option<&ProfileProgram>,
    id_inputs: &BTreeMap<VarId, String>,
) -> Result<BTreeMap<VarId, Fp>> {
    let assign_fp = xark_ir::solver::solve_and_check(prim, id_inputs).map_err(|e| {
        // A missing input names the *declared* input the user actually types,
        // e.g. `MissingInput(1)` → "missing input `result`". Every other failure
        // defers to the shared diagnostic, which names the failing constraint
        // (and its source line / gadget when profiled) — the same explanation
        // `xark test` surfaces.
        if let xark_ir::solver::SolveError::MissingInput(id) = e
            && let Some(v) = prim.vars.iter().find(|v| v.id == id)
        {
            return anyhow::anyhow!(
                "missing input `{0}` (add it to --inputs, e.g. --inputs '{{\"{0}\": <value>}}')",
                v.name
            );
        }
        anyhow::anyhow!(
            "{}",
            xark_ir::diagnose::describe_unsatisfied(&e, r1cs, profile)
        )
    })?;
    report_underconstrained(xark_ir::solver::analyze_underconstrained(prim, &assign_fp))?;
    Ok(assign_fp)
}

/// `bail!` with the shared under-constraint diagnostic if any hole was found.
fn report_underconstrained(holes: Vec<xark_ir::solver::UnderConstrained>) -> Result<()> {
    if !holes.is_empty() {
        let mut msg = crate::style::err(
            "circuit is under-constrained: a malicious prover could forge the \
             following derived variable(s) without violating any constraint, so \
             any proof of this circuit is unsound:",
        );
        for h in &holes {
            msg.push_str(&format!("\n  - `{}` (var {}): {}", h.name, h.var, h.reason));
        }
        msg.push_str(
            "\nevery hint/advice value (`hint_inverse`, `hint_bit`, `advice`, the \
             bignum hints) must be pinned by a constraint (e.g. `require_eq`).",
        );
        anyhow::bail!(msg);
    }
    Ok(())
}

/// The number of public inputs the circuit exposes.
pub fn num_public_inputs(prog: &R1csProgram) -> usize {
    prog.variables
        .iter()
        .filter(|v| v.visibility == Visibility::Public)
        .count()
}

/// SHA-256 of arbitrary bytes, hex-encoded (no `0x`). Used to fingerprint a
/// proof so it can be referenced/tracked and content-addressed on disk.
pub fn sha256_hex(bytes: &[u8]) -> String {
    use sha2::{Digest, Sha256};
    hex::encode(Sha256::digest(bytes))
}

/// A stable circuit identifier: the SHA-256 (hex) of the `r1cs.json` text.
pub fn circuit_hash(r1cs_json: &str) -> String {
    sha256_hex(r1cs_json.as_bytes())
}

/// Public inputs in variable-id (allocation) order, taken from `--inputs`
/// values. This matches how the prover derives them from the solved witness:
/// the public portion of the assignment, in var-id order.
pub fn public_inputs_from_inputs(
    prog: &R1csProgram,
    inputs: &BTreeMap<String, String>,
) -> Result<Vec<Fr>> {
    let mut vars: Vec<_> = prog
        .variables
        .iter()
        .filter(|v| v.visibility == Visibility::Public)
        .collect();
    vars.sort_by_key(|v| v.id);
    let mut out = Vec::with_capacity(vars.len());
    for v in vars {
        let value = inputs.get(&v.name).with_context(|| {
            format!(
                "missing public input `{0}` (add it to --inputs, e.g. --inputs '{{\"{0}\": <value>}}')",
                v.name
            )
        })?;
        let fr = xark_prover::try_fr_from_decimal(value)
            .map_err(|e| anyhow::anyhow!("public input `{}`: {e}", v.name))?;
        out.push(fr);
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::{inputs_hint, parse_input_text, parse_inputs_arg};
    use std::path::Path;

    #[test]
    fn parses_line_input_file() {
        let inputs = parse_input_text(
            "# witness\npath[0] = 12\namount = '34' # inline comment\n",
            Path::new("witness.inputs"),
        )
        .unwrap();

        assert_eq!(inputs.get("path[0]").map(String::as_str), Some("12"));
        assert_eq!(inputs.get("amount").map(String::as_str), Some("34"));
    }

    #[test]
    fn parses_json_without_losing_large_values() {
        let inputs = parse_input_text(
            r#"{"amount": 34, "field": "21888242871839275222246405745257275088548364400416034343698204186575808495616"}"#,
            Path::new("witness.json"),
        )
        .unwrap();

        assert_eq!(inputs.get("amount").map(String::as_str), Some("34"));
        assert_eq!(
            inputs.get("field").map(String::as_str),
            Some("21888242871839275222246405745257275088548364400416034343698204186575808495616")
        );
    }

    #[test]
    fn rejects_non_scalar_json_values() {
        let err = parse_input_text(r#"{"path": [1, 2]}"#, Path::new("witness.json")).unwrap_err();

        assert!(
            err.to_string()
                .contains("input `path` must be a decimal string or number")
        );
    }

    #[test]
    fn inputs_arg_accepts_inline_json() {
        // A leading `{` is read as inline JSON — no file on disk.
        let inputs = parse_inputs_arg(r#"{"secret": 3, "result": 27}"#).unwrap();
        assert_eq!(inputs.get("secret").map(String::as_str), Some("3"));
        assert_eq!(inputs.get("result").map(String::as_str), Some("27"));
    }

    #[test]
    fn inputs_arg_reads_a_file_path() {
        let dir = std::env::temp_dir().join("xark-inputs-arg-test");
        std::fs::create_dir_all(&dir).unwrap();
        let path = dir.join("w.inputs");
        std::fs::write(&path, "secret = 3\nresult = 27\n").unwrap();

        let inputs = parse_inputs_arg(path.to_str().unwrap()).unwrap();
        assert_eq!(inputs.get("secret").map(String::as_str), Some("3"));
        assert_eq!(inputs.get("result").map(String::as_str), Some("27"));
    }

    #[test]
    fn hint_renders_a_json_template() {
        assert_eq!(
            inputs_hint(&["secret", "result"]),
            r#"--inputs '{"secret": <value>, "result": <value>}'"#
        );
    }
}
