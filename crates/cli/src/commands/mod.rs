//! The clap-driven `xark` CLI.
//!
//! Frontend subcommands (`init`/`build`/`check`) drive `cargo` (for wasm32) and
//! the frontend; their implementations live in [`crate::cli`]. Backend subcommands
//! (`setup`/`prove`/`verify`/`export`/`ceremony`/`inspect`) read the xark-IR
//! produced by `xark build` and run the shared Groth16 backend.

use std::collections::BTreeMap;

use anyhow::{Context, Result};
use ark_bn254::Fr;
use clap::{Parser, Subcommand};
use tracing_subscriber::EnvFilter;

use xark_ir::SourceMap;
use xark_ir::primitive::PrimitiveProgram;
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

/// `xark` — write, compile, prove and verify zero-knowledge circuits in Rust.
#[derive(Parser, Debug)]
#[command(
    name = "xark",
    version = concat!(env!("CARGO_PKG_VERSION"), " (", env!("XARK_GIT_HASH"), ")"),
    styles = crate::style::clap_styles(),
    about = "Write, compile, prove and verify zero-knowledge circuits in Rust",
    long_about = "xark compiles a Rust circuit (built for wasm32 with any stable \
toolchain) into xark-IR + R1CS, then proves and verifies it with Groth16 over \
BN254. `xark build` emits `circuit.xbc` under `<crate>/target/xark/`; the \
backend commands read it from there automatically."
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
    /// Compile a circuit crate (Rust → wasm32 → R1CS) into target/xark/.
    Build(BuildArgs),
    /// Validate a circuit crate and report subset rejections as diagnostics.
    Check(CheckArgs),
    /// Build the circuit, then run its `cargo test` circuit tests.
    Test(TestArgs),
    /// Remove all xark build output (every `target/xark/`, `target/xark-wasm/` and
    /// `target/xark-client/` under the current dir).
    Clean(CleanArgs),
    /// Generate Groth16 proving and verifying keys.
    Setup(setup::SetupArgs),
    /// Solve the witness from --inputs values and produce a Groth16 proof.
    Prove(prove::ProveArgs),
    /// Verify a Groth16 proof against public inputs.
    Verify(verify::VerifyArgs),
    /// Export a self-contained Solana verifier crate.
    Export(export::ExportArgs),
    /// Generate a typed TypeScript client from the build's `schema.json` (prove +
    /// verify through xark-wasm; builds the circuit if needed, no setup or proof).
    Client(client::ClientArgs),
    /// Phase-2 MPC ceremony for trusted setup.
    Ceremony(ceremony::CeremonyArgs),
    /// Print circuit statistics (variables, constraints, public inputs), building
    /// the circuit first if it's missing or stale.
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
        Command::Build(a) => exit_code("build", crate::cli::cmd_build_command(&a.to_argv())),
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
    /// Output directory for the build artifacts (`circuit.xbc`, `schema.json`, …;
    /// default: `<crate>/target/xark/<name>/`).
    #[arg(long, value_hint = clap::ValueHint::DirPath)]
    pub out: Option<String>,
    /// Field the circuit is defined over: `bn254` (the one Groth16 keys and proofs
    /// use), or a prime modulus in decimal (to count constraints over another field).
    #[arg(long, default_value = "bn254", value_parser = parse_field)]
    pub field: String,
    /// Also write `circuit.json` and `r1cs.json`, human-readable views of the
    /// circuit for debugging. Every command reads `circuit.xbc`; the JSON is
    /// never read back, and is multi-GB on large circuits, so it's off by default.
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
    /// Circuit inputs as inline JSON `{"name": value, …}` or a path to an input
    /// file. Passing `--inputs` opts into the witness-based under-constrained
    /// soundness check: xark builds the circuit, solves the witness from these
    /// inputs, and reports any derived variable the constraints fail to pin.
    /// Provide every circuit input, as `xark prove` does. With no `--inputs`,
    /// `check` stays the fast validator.
    #[arg(long = "inputs", value_name = "JSON|FILE")]
    pub inputs: Option<String>,
    /// Output directory for the build `--inputs` runs (default:
    /// `<crate>/target/xark/<name>/`). Only used with `--inputs`.
    #[arg(long, value_hint = clap::ValueHint::DirPath)]
    pub out: Option<String>,
}

impl CheckArgs {
    fn to_argv(&self) -> Vec<String> {
        let mut v = vec![self.crate_dir.clone()];
        if self.message_format.as_deref() == Some("json") {
            v.push("--message-format=json".into());
        }
        v
    }
}

#[derive(clap::Args, Debug)]
pub struct TestArgs {
    /// Circuit crate directory to build and test.
    #[arg(default_value = ".", value_hint = clap::ValueHint::DirPath)]
    pub crate_dir: String,
    /// Arguments for `cargo test`, passed through verbatim, as you'd give them to
    /// `cargo test` itself: a test-name filter, cargo flags, and after `--` the
    /// test binary's (`xark test . -- --include-ignored`).
    #[arg(trailing_var_arg = true, allow_hyphen_values = true)]
    pub cargo_args: Vec<String>,
}

impl TestArgs {
    /// `[crate dir, cargo test args…]`, read from the raw command line: clap
    /// swallows a `--` that `cargo test` needs (`xark test . -- --list` must reach
    /// cargo as `-- --list`). The first argument is the crate dir if it is one or
    /// looks like a path (so a mistyped path is reported, not taken as a filter);
    /// `xark test my_test` filters in the current crate.
    fn to_argv(&self) -> Vec<String> {
        let raw: Vec<String> = std::env::args().collect();
        let Some(i) = raw.iter().skip(1).position(|a| a == "test") else {
            let mut v = vec![self.crate_dir.clone()];
            v.extend(self.cargo_args.iter().cloned());
            return v;
        };
        let rest = &raw[i + 2..];
        match rest.first() {
            Some(d)
                if !d.starts_with('-')
                    && (std::path::Path::new(d).is_dir() || looks_like_path(d)) =>
            {
                rest.to_vec()
            }
            _ => std::iter::once(".".to_string())
                .chain(rest.iter().cloned())
                .collect(),
        }
    }
}

/// A path rather than a test-name filter: test names never hold a separator or
/// start with `.` or `~`.
fn looks_like_path(s: &str) -> bool {
    s.contains('/') || s.contains(std::path::MAIN_SEPARATOR) || s.starts_with(['.', '~'])
}

// Shared helpers for the backend commands.

/// Read the artifact at `path` with `read`, saying plainly what's wrong when it
/// fails: missing (`missing` says what makes it), empty, or not a `what` at all
/// (`by` wrote the real one; the decoder's error follows, as the detail).
pub fn read_artifact<T, E: std::fmt::Display>(
    path: &std::path::Path,
    what: &str,
    by: &str,
    missing: &str,
    read: impl FnOnce() -> std::result::Result<T, E>,
) -> Result<T> {
    read().map_err(|e| match std::fs::metadata(path) {
        Err(_) => anyhow::anyhow!("no {what} at {} ({missing})", path.display()),
        Ok(m) if m.len() == 0 => {
            anyhow::anyhow!(
                "{} is empty: it isn't a {what} written by `{by}`",
                path.display()
            )
        }
        Ok(_) => {
            // A truncated file: the decoder reports the io error's debug form.
            let e = e.to_string();
            let detail = if e.contains("UnexpectedEof") || e.contains("failed to fill whole buffer")
            {
                "it's cut short".to_string()
            } else {
                e
            };
            anyhow::anyhow!(
                "{} isn't a {what} written by `{by}` ({detail})",
                path.display()
            )
        }
    })
}

/// `--field`: `bn254` (or `bn128`), or a prime modulus in decimal; normalized.
pub fn parse_field(s: &str) -> std::result::Result<String, String> {
    let f = xark_ir::FieldSpec::parse(s)?;
    Ok(match f.name.as_str() {
        "bn254" => "bn254".into(),
        _ => f.modulus_decimal.unwrap_or_default(),
    })
}

/// Render the path argument the user passed (for the guided "Next:" hints) so
/// suggested commands are copy-pasteable. Falls back to `.` when none was given.
pub fn path_arg(path: &Option<std::path::PathBuf>) -> String {
    match path {
        Some(p) => p.display().to_string(),
        None => ".".to_string(),
    }
}

/// Warn that `--out` directory `dir` isn't empty (when it holds anything): what a
/// command writes there replaces any file of the same name.
pub fn warn_if_not_empty(dir: &std::path::Path, what: &str) {
    if std::fs::read_dir(dir).is_ok_and(|mut d| d.next().is_some()) {
        eprintln!(
            "{} {} isn't empty: writing the {what} there anyway, replacing any already there",
            crate::style::warn("warning:"),
            dir.display()
        );
    }
}

/// `path` as a command line takes it: relative to the current directory when under it.
pub fn shown(path: &std::path::Path) -> String {
    let cwd = std::env::current_dir().unwrap_or_default();
    path.strip_prefix(&cwd)
        .unwrap_or(path)
        .display()
        .to_string()
}

/// The circuit's `schema.json`, if the build wrote a current one (for summaries
/// and hints).
pub fn load_schema(xark_dir: &std::path::Path) -> Option<xark_schema::Schema> {
    require_schema(xark_dir).ok()
}

/// The circuit's `schema.json`: how `--inputs` values are read. Missing, or written
/// by an older xark: rebuild.
pub fn require_schema(xark_dir: &std::path::Path) -> Result<xark_schema::Schema> {
    let path = xark_dir.join("schema.json");
    let text = std::fs::read_to_string(&path).map_err(|_| {
        anyhow::anyhow!(
            "no {} (it describes the circuit's inputs): run `xark build`",
            path.display()
        )
    })?;
    xark_schema::Schema::parse(&text).map_err(|e| anyhow::anyhow!("{}: {e}", path.display()))
}

/// `--inputs` as a JSON object: inline JSON (a leading `{`), or a file of JSON or
/// `name = value` lines.
fn inputs_json(arg: &str) -> Result<serde_json::Value> {
    let (text, source) = if arg.trim_start().starts_with('{') {
        (arg.to_string(), "<--inputs>".to_string())
    } else {
        let t = std::fs::read_to_string(arg)
            .with_context(|| format!("reading --inputs file `{arg}`"))?;
        (t, arg.to_string())
    };
    if text.trim_start().starts_with('{') {
        return serde_json::from_str(&text).with_context(|| format!("parsing {source} as JSON"));
    }
    let map: serde_json::Map<String, serde_json::Value> =
        parse_input_text(&text, std::path::Path::new(&source))?
            .into_iter()
            .map(|(k, v)| (k, serde_json::Value::String(v)))
            .collect();
    Ok(serde_json::Value::Object(map))
}

/// `--inputs` as the circuit's input leaves (`name → decimal`), every value taken in
/// its type's natural form (a date as `"YYYY-MM-DD"`, a key as its bytes) and checked
/// against `schema.json` (a `uN` against its range, a field element against `p`).
pub fn read_inputs(xark_dir: &std::path::Path, arg: &str) -> Result<BTreeMap<String, String>> {
    let leaves = require_schema(xark_dir)?
        .leaves(&inputs_json(arg)?)
        .map_err(|e| anyhow::anyhow!(e))?;
    Ok(leaves
        .into_iter()
        .map(|(k, v)| (k, v.to_string()))
        .collect())
}

/// `--inputs` as the public inputs, in proof order (only the public ones need be
/// given).
pub fn read_public_inputs(xark_dir: &std::path::Path, arg: &str) -> Result<Vec<Fr>> {
    require_schema(xark_dir)?
        .public_inputs(&inputs_json(arg)?)
        .map_err(|e| anyhow::anyhow!(e))
}

/// Parse an inputs file of `name = value` lines (`#` comments and blank lines
/// ignored). A name may be a nested path (`id.born`, `msg[0]`), as `--inputs` JSON
/// keys may.
pub fn parse_input_text(text: &str, source: &std::path::Path) -> Result<BTreeMap<String, String>> {
    let mut out = BTreeMap::new();
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

/// True if `bytes` is a current `XBC` circuit container: version 2, what `xark
/// build` writes. (Version 1 came from the removed MIR frontend: rebuild.) The
/// magic + u16 version guard rejects stale/foreign files so every loader can
/// dispatch on it.
pub fn is_function_artifact(bytes: &[u8]) -> bool {
    bytes.len() >= 6 && bytes[0..4] == *b"XBC\0" && u16::from_le_bytes([bytes[4], bytes[5]]) == 2
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

/// Load the Groth16 backend's [`R1csProgram`] from a built `circuit.xbc`, with
/// the SHA-256 fingerprint of its bytes (the key metadata's circuit hash).
pub fn load_backend_r1cs(xbc_path: &std::path::Path) -> Result<(R1csProgram, String)> {
    let bytes = std::fs::read(xbc_path)
        .with_context(|| format!("reading {} (run `xark build` first?)", xbc_path.display()))?;
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
    Ok((cp.into_r1cs(), fingerprint))
}

/// Load the solver-facing [`PrimitiveProgram`] from a `circuit.xbc`.
pub fn load_primitive(path: &std::path::Path) -> Result<PrimitiveProgram> {
    load_circuit_program(path).map(|cp| cp.to_primitive())
}

/// Best-effort load of `sources.json` (each constraint's source statement) from a
/// build directory, so a failing constraint names its line. `None` for a build
/// from before it existed, or a malformed file.
pub fn load_sources(dir: &std::path::Path) -> Option<SourceMap> {
    SourceMap::load(dir)
}

/// Resolve `name → value` inputs to `VarId → decimal` for the solver. Shared by
/// `xark prove` and `xark check --inputs`; the logic lives in
/// [`xark_prover::resolve_input_ids`] so the wasm prover accepts exactly the same inputs.
pub fn resolve_input_ids(
    vars: &[xark_ir::primitive::Var],
    inputs: &BTreeMap<String, String>,
) -> Result<BTreeMap<VarId, String>> {
    xark_prover::resolve_input_ids(vars, inputs).map_err(anyhow::Error::msg)
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
    sources: Option<&SourceMap>,
    id_inputs: &BTreeMap<VarId, String>,
) -> Result<BTreeMap<VarId, Fp>> {
    // Solve + check directly on the R1CS rows (no `to_primitive` flattening). On
    // an unsatisfied witness, name *which* constraint (and its
    // source line / function) failed — the same explanation `xark test` surfaces;
    // the R1CS is materialized only here, on the (rare) error path.
    let describe = |e| {
        let r1cs = cp.to_r1cs();
        anyhow::anyhow!(
            "{}",
            xark_ir::diagnose::describe_unsatisfied(&e, &r1cs, sources)
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

/// **Streaming** witness solve + soundness gate for the default `xark prove`
/// path, straight from the compact `circuit.xbc` bytes — never materializing the
/// full flat program (`witness_gen` is the multi-GB bulk on non-native
/// folding/IVC circuits). Returns the witness assignment for the Groth16 backend.
///
/// The happy path holds only the witness + a flag byte per var. On the rare
/// failure path (the witness does not satisfy the circuit, or solving fails) it
/// re-expands the flat program once and defers to [`soundness_check`] for the
/// precise which-constraint / source-line diagnostic — trading memory for a good
/// error message exactly when a proof is going to fail anyway.
pub fn stream_soundness(
    bytes: &[u8],
    sources: Option<&SourceMap>,
    id_inputs: &BTreeMap<VarId, String>,
) -> Result<BTreeMap<VarId, Fp>> {
    let timing = dbg_flag("PROVE_TIME");
    let t = std::time::Instant::now();
    match xark_ir::function_decode::stream_solve_verify(bytes, id_inputs) {
        Ok((assign_fp, holes)) => {
            if timing {
                eprintln!("PROVE_TIME:   stream solve+check+analyze={:?}", t.elapsed());
            }
            report_underconstrained(holes)?;
            Ok(assign_fp)
        }
        Err(_) => {
            // Rare: unsatisfied/solve error. Re-expand flat for the rich diagnostic
            // (same explanation `xark test` surfaces); on success (shouldn't differ
            // from the stream) just return its assignment.
            let cp = xark_ir::function_decode::expand_function_blob(bytes)
                .map_err(|e| anyhow::anyhow!(e))?;
            soundness_check(&cp, sources, id_inputs)
        }
    }
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

/// The R1CS digest of a `circuit.xbc` (what `xark build` prints): the same for every
/// build of a circuit, whichever Rust compiled it.
pub fn r1cs_digest(xbc: &[u8]) -> String {
    xark_ir::function_decode::stream_digest_hex(xbc)
}

/// How a key (by the `metadata.json` beside it) relates to a `circuit.xbc`.
#[derive(Debug, PartialEq)]
pub enum KeyFit {
    /// Made from this very file, or nothing to compare (no metadata, or no build).
    Same,
    /// Made from another build of the same constraint system (another Rust version
    /// laid out `circuit.xbc` differently): it fits. The prover's self-check still
    /// catches a key whose rows turn out not to.
    SameCircuit,
    /// Made for a different circuit.
    Different,
}

/// Whether the key at `key` was made for the circuit in `xbc` (its bytes).
pub fn key_fit(key: &std::path::Path, xbc: &[u8]) -> KeyFit {
    let Some(meta) = key
        .parent()
        .and_then(|dir| std::fs::read_to_string(dir.join("metadata.json")).ok())
        .and_then(|s| serde_json::from_str::<serde_json::Value>(&s).ok())
    else {
        return KeyFit::Same;
    };
    let field = |k: &str| meta.get(k).and_then(|v| v.as_str()).map(str::to_string);
    match (field("circuit_hash"), field("digest")) {
        (None, _) => KeyFit::Same,
        (Some(h), _) if h == sha256_hex(xbc) => KeyFit::Same,
        (_, Some(d)) if d == r1cs_digest(xbc) => KeyFit::SameCircuit,
        _ => KeyFit::Different,
    }
}

/// Refuse a key made for a different circuit (see [`key_fit`]). No check when the
/// metadata or the build is missing (keys copied alone, or shipped without the build).
pub fn ensure_key_matches_circuit(key: &std::path::Path, xbc: &std::path::Path) -> Result<()> {
    let Ok(bytes) = std::fs::read(xbc) else {
        return Ok(());
    };
    if key_fit(key, &bytes) == KeyFit::Different {
        anyhow::bail!(
            "the key {} was made for a different build of the circuit (the circuit \
             changed since `xark setup`): run `xark setup` and `xark prove` again",
            key.display()
        );
    }
    Ok(())
}

/// The SHA-256 (hex) of a string (e.g. a phase-2 seed, recorded in key metadata).
pub fn circuit_hash(r1cs_json: &str) -> String {
    sha256_hex(r1cs_json.as_bytes())
}

#[cfg(test)]
mod tests {
    use super::{inputs_hint, parse_input_text, read_inputs};
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

    /// `--inputs` is read against `schema.json`: values in natural forms, ranges
    /// checked, and a missing or old schema asks for a rebuild.
    #[test]
    fn inputs_follow_the_schema() {
        let dir = std::env::temp_dir().join(format!("xark-inputs-test-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let missing = read_inputs(&dir, r#"{"b": 1}"#).unwrap_err().to_string();
        assert!(missing.contains("run `xark build`"), "{missing}");
        std::fs::write(dir.join("schema.json"), r#"{"version": 1, "inputs": []}"#).unwrap();
        let old = read_inputs(&dir, r#"{"b": 1}"#).unwrap_err().to_string();
        assert!(old.contains("rebuild"), "{old}");
        std::fs::write(
            dir.join("schema.json"),
            r#"{"version": 2, "circuit": "c",
              "inputs": [{"name": "b", "visibility": "private", "type": {"uint": 8}},
                         {"name": "msg", "visibility": "public", "type": {"array": {"of": {"uint": 8}, "len": 2}}}],
              "types": {}, "public_inputs": ["msg[0]", "msg[1]"]}"#,
        )
        .unwrap();
        let leaves = read_inputs(&dir, r#"{"b": 255, "msg": "0x6162"}"#).unwrap();
        assert_eq!(
            (leaves["b"].as_str(), leaves["msg[1]"].as_str()),
            ("255", "98")
        );
        let err = read_inputs(&dir, r#"{"b": 256, "msg": "0x6162"}"#)
            .unwrap_err()
            .to_string();
        assert!(err.contains("out of range for a u8"), "{err}");
        let file = dir.join("w.inputs");
        std::fs::write(&file, "b = 7\nmsg[0] = 1\nmsg[1] = 2\n").unwrap();
        assert_eq!(read_inputs(&dir, file.to_str().unwrap()).unwrap()["b"], "7");
        std::fs::remove_dir_all(&dir).unwrap();
    }

    #[test]
    fn hint_renders_a_json_template() {
        assert_eq!(
            inputs_hint(&["secret", "result"]),
            r#"--inputs '{"secret": <value>, "result": <value>}'"#
        );
    }
}
