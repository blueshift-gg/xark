use std::fs;
use std::path::PathBuf;

use anyhow::{Context, Result};
use clap::{Args, Subcommand};

use groth16_backend::evm::export_verifier_solidity;
use groth16_backend::keys::Groth16Keys;

use super::export_solana::{self, SolanaArgs};

#[derive(Args, Debug)]
pub struct ExportArgs {
    #[command(subcommand)]
    pub target: ExportTarget,
}

#[derive(Subcommand, Debug)]
pub enum ExportTarget {
    /// Export a single-file Solidity Groth16 verifier for the EVM.
    Evm(EvmArgs),
    /// Export Solana on-chain wire bytes (VK + proof + public inputs) for the
    /// `xark-solana-verifier` program.
    Solana(SolanaArgs),
}

#[derive(Args, Debug)]
pub struct EvmArgs {
    /// Path to the verifying key (canonical binary format).
    #[arg(long)]
    pub verifying_key: PathBuf,
    /// Path to write the generated `Verifier.sol`.
    #[arg(long)]
    pub out: PathBuf,
}

pub fn run(args: ExportArgs) -> Result<()> {
    match args.target {
        ExportTarget::Evm(evm_args) => run_evm(evm_args),
        ExportTarget::Solana(solana_args) => export_solana::run(solana_args),
    }
}

fn run_evm(args: EvmArgs) -> Result<()> {
    let vk = Groth16Keys::read_verifying_key(&args.verifying_key)
        .with_context(|| format!("reading verifying key {}", args.verifying_key.display()))?;
    let source = export_verifier_solidity(&vk).context("generating Solidity verifier")?;
    fs::write(&args.out, source).with_context(|| format!("writing {}", args.out.display()))?;
    let num_inputs = vk.gamma_abc_g1.len().saturating_sub(1);
    println!(
        "Wrote Solidity verifier to {} ({} public input(s))",
        args.out.display(),
        num_inputs
    );
    Ok(())
}
