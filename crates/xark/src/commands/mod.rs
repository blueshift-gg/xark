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

use xark_ir::primitive::PrimitiveProgram;
use xark_ir::{R1csProgram, Visibility};

pub mod ceremony;
pub mod completions;
pub mod export;
pub mod inspect;
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
    version,
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
    /// Solve the witness from --input values and produce a Groth16 proof.
    Prove(prove::ProveArgs),
    /// Verify a Groth16 proof against public inputs.
    Verify(verify::VerifyArgs),
    /// Export a self-contained Solana verifier crate.
    Export(export::ExportArgs),
    /// Phase-2 MPC ceremony for trusted setup.
    Ceremony(ceremony::CeremonyArgs),
    /// Print circuit statistics (variables, constraints, public inputs).
    Inspect(inspect::InspectArgs),
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
            eprintln!("error: {e:#}");
            1
        }
    };
    std::process::exit(code);
}

fn run(cli: Cli) -> Result<()> {
    match cli.command {
        // Frontend commands delegate to the hand-rolled `cargo`-driving
        // implementations, which return a process exit code.
        Command::Init(a) => exit_code("init", crate::cli::cmd_init(&a.to_argv())),
        Command::Build(a) => exit_code("build", crate::cli::cmd_build(&a.to_argv())),
        Command::Check(a) => exit_code("check", crate::cli::cmd_check(&a.to_argv())),
        Command::Test(a) => exit_code("test", crate::cli::cmd_test(&a.to_argv())),
        Command::Clean(a) => exit_code("clean", crate::cli::cmd_clean(&a.to_argv())),
        // Backend commands are `anyhow`-based.
        Command::Setup(a) => setup::run(a),
        Command::Prove(a) => prove::run(a),
        Command::Verify(a) => verify::run(a),
        Command::Export(a) => export::run(a),
        Command::Ceremony(a) => ceremony::run(a),
        Command::Inspect(a) => inspect::run(a),
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

/// Parse `--input name=value` pairs into a name→value map.
pub fn parse_inputs(pairs: &[String]) -> Result<BTreeMap<String, String>> {
    let mut inputs = BTreeMap::new();
    for kv in pairs {
        let (k, v) = kv
            .split_once('=')
            .with_context(|| format!("--input expects name=value, got `{kv}`"))?;
        inputs.insert(k.to_string(), v.to_string());
    }
    Ok(inputs)
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

/// The number of public inputs the circuit exposes.
pub fn num_public_inputs(prog: &R1csProgram) -> usize {
    prog.variables
        .iter()
        .filter(|v| v.visibility == Visibility::Public)
        .count()
}

/// A stable circuit identifier: the SHA-256 (hex) of the `r1cs.json` text.
pub fn circuit_hash(r1cs_json: &str) -> String {
    use sha2::{Digest, Sha256};
    hex::encode(Sha256::digest(r1cs_json.as_bytes()))
}

/// Public inputs in variable-id (allocation) order, taken from `--input`
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
                "missing public input `{}` (pass --input {}=<value>)",
                v.name, v.name
            )
        })?;
        let fr = xark_prover::try_fr_from_decimal(value)
            .map_err(|e| anyhow::anyhow!("public input `{}`: {e}", v.name))?;
        out.push(fr);
    }
    Ok(out)
}
