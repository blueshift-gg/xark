//! The clap-driven `xark` CLI.
//!
//! `xark` is a dual-role binary: when cargo invokes it as `RUSTC` during
//! `xark build` it drives `rustc_driver` (see `crate::run_as_rustc`); when a
//! user runs one of the known subcommands it behaves as this toolchain CLI.
//! `crate::main` dispatches between the two before clap ever sees the args, so
//! clap never tries to parse a rustc invocation.
//!
//! The frontend subcommands (`init`/`build`/`check`) drive `cargo` with `xark`
//! as `RUSTC`; their implementations live in [`crate::cli`]. The backend
//! subcommands (`setup`/`prove`/`verify`/`export`/`ceremony`/`inspect`) read
//! the xark-IR (`circuit.json` + `r1cs.json`) produced by `xark build` and run
//! the shared Arkworks Groth16 backend (`xark_backend`).

use std::collections::BTreeMap;

use anyhow::{Context, Result};
use ark_bn254::Fr;
use clap::{Parser, Subcommand};
use tracing_subscriber::EnvFilter;

use xark_ir::primitive::{PrimitiveProgram, VarRole};
use xark_ir::profile::ProfileProgram;
use xark_ir::solver::Fp;
use xark_ir::{R1csProgram, VarId, Visibility};

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
    /// Profile a circuit: attribute each constraint to its source line, gadget
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

// -- Frontend argument structs (delegate to `crate::cli`) ---------------------

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

// -- Shared helpers for the backend commands ----------------------------------

/// Render the path argument the user passed (for the guided "Next:" hints), so
/// suggested commands are copy-pasteable verbatim. Falls back to `.` (the
/// current directory) when no path was given, matching the commands' defaults.
pub fn path_arg(path: &Option<std::path::PathBuf>) -> String {
    match path {
        Some(p) => p.display().to_string(),
        None => ".".to_string(),
    }
}

/// Parse the `--inputs` argument: either an inline JSON object
/// `{ "name": value, … }` or a path to a file (a JSON object, or `name = value`
/// lines with `#` comments and blank lines ignored). Array elements use the flat
/// names `xark inspect` prints, e.g. `path[0]`. A leading `{` (after trimming)
/// selects inline JSON; anything else is treated as a file path — so the one
/// argument is agnostic to how you pass the witness.
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

/// Best-effort load of `profile.json` (per-constraint source/gadget attribution)
/// from a build directory, for richer failure diagnostics. Returns `None` when
/// the circuit was built without `--profile` (or the file is malformed).
pub fn load_profile(dir: &std::path::Path) -> Option<ProfileProgram> {
    std::fs::read_to_string(dir.join("profile.json"))
        .ok()
        .and_then(|s| xark_ir::profile::from_json(&s).ok())
}

/// Resolve `name → value` inputs to `VarId → decimal` for the solver.
///
/// Shared by `xark prove` and `xark check --inputs`: applies the same strict
/// decimal validation (the solver's lenient parse would silently turn a
/// malformed value into 0) and the same unknown-name error (listing the
/// circuit's non-derived inputs).
pub fn resolve_input_ids(
    prim: &PrimitiveProgram,
    inputs: &BTreeMap<String, String>,
) -> Result<BTreeMap<VarId, String>> {
    let by_name: BTreeMap<&str, VarId> =
        prim.vars.iter().map(|v| (v.name.as_str(), v.id)).collect();
    let mut id_inputs: BTreeMap<VarId, String> = BTreeMap::new();
    for (k, v) in inputs {
        match by_name.get(k.as_str()) {
            Some(&id) => {
                xark_prover::try_fr_from_decimal(v)
                    .map_err(|e| anyhow::anyhow!("invalid value for input `{k}`: {e}"))?;
                id_inputs.insert(id, v.clone());
            }
            None => {
                let names: Vec<&String> = prim
                    .vars
                    .iter()
                    .filter(|v| !matches!(v.role, VarRole::Derived))
                    .map(|v| &v.name)
                    .collect();
                anyhow::bail!("unknown input `{k}` (circuit inputs: {names:?})");
            }
        }
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
/// with a clear message listing each hole. On success it returns the solved
/// assignment.
///
/// This is the *witness-based* check: it needs the solved assignment (hence it
/// runs after solving, before any key-loading / synthesis). It rejects circuits
/// with a derived variable the constraints fail to pin uniquely. A structural,
/// witness-free version at `xark build`/`check` is planned.
pub fn soundness_check(
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
        if let xark_ir::solver::SolveError::MissingInput(id) = e {
            if let Some(v) = prim.vars.iter().find(|v| v.id == id) {
                return anyhow::anyhow!(
                    "missing input `{0}` (add it to --inputs, e.g. --inputs '{{\"{0}\": <value>}}')",
                    v.name
                );
            }
        }
        anyhow::anyhow!(
            "{}",
            xark_ir::diagnose::describe_unsatisfied(&e, r1cs, profile)
        )
    })?;

    let holes = xark_ir::solver::analyze_underconstrained(prim, &assign_fp);
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
             bignum hints) must be pinned by a constraint (e.g. `assert_eq`).",
        );
        anyhow::bail!(msg);
    }
    Ok(assign_fp)
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

        assert!(err
            .to_string()
            .contains("input `path` must be a decimal string or number"));
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
