use anyhow::Result;
use clap::{Parser, Subcommand};

/// Convert an arkworks `SynthesisError` into an `anyhow::Error`. ark types are
/// no_std and don't implement `std::error::Error`, so we wrap via their
/// `Display` impl.
pub fn synth_err(e: ark_relations::r1cs::SynthesisError) -> anyhow::Error {
    anyhow::anyhow!("R1CS synthesis error: {e}")
}

pub mod ceremony;
pub mod export;
pub mod export_solana;
pub mod inspect;
pub mod prove;
pub mod setup;
pub mod verify;
pub mod write_vk;

/// `xark` — a Rust Groth16 backend for Noir on BN254.
#[derive(Parser, Debug)]
#[command(
    name = "xark",
    version,
    about = "Rust Groth16 (BN254) backend for Noir",
    long_about = "xark consumes Noir/ACIR artifacts, lowers supported opcodes \
                  into R1CS, and proves/verifies them using Arkworks Groth16 over BN254."
)]
pub struct Cli {
    #[command(subcommand)]
    pub command: Command,
}

#[derive(Subcommand, Debug)]
pub enum Command {
    Inspect(inspect::InspectArgs),
    Setup(setup::SetupArgs),
    Prove(prove::ProveArgs),
    Verify(verify::VerifyArgs),
    WriteVk(write_vk::WriteVkArgs),
    Export(export::ExportArgs),
    Ceremony(ceremony::CeremonyArgs),
}

impl Cli {
    pub fn run(self) -> Result<()> {
        match self.command {
            Command::Inspect(args) => inspect::run(args),
            Command::Setup(args) => setup::run(args),
            Command::Prove(args) => prove::run(args),
            Command::Verify(args) => verify::run(args),
            Command::WriteVk(args) => write_vk::run(args),
            Command::Export(args) => export::run(args),
            Command::Ceremony(args) => ceremony::run(args),
        }
    }
}
