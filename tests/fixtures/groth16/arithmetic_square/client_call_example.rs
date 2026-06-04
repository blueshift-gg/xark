//! Submit an xark-exported Groth16 proof to the on-chain verifier program.
//!
//! Workflow:
//!
//! 1. Embed `verifying_key.solana.bin` in your on-chain program crate
//!    via `xark_solana_verifier::xark_groth16_program! { vk: include_bytes!("vk.bin"), }`.
//! 2. Deploy the program (one program ID per VK).
//! 3. From the client, submit `instruction_data.bin` as the instruction
//!    data — just `proof_bytes || public_inputs`, no VK.
//!
//! Copy this file into a fresh Cargo project with:
//!
//! ```toml
//! [dependencies]
//! solana-client = "2"
//! solana-sdk = "2"
//! anyhow = "1"
//! ```

use std::str::FromStr;

use anyhow::Result;
use solana_client::rpc_client::RpcClient;
use solana_sdk::{
    commitment_config::CommitmentConfig,
    instruction::Instruction,
    pubkey::Pubkey,
    signature::{read_keypair_file, Signer},
    transaction::Transaction,
};

// ---- Fill these in ---------------------------------------------------------
const PROGRAM_ID: &str = "REPLACE_WITH_DEPLOYED_PROGRAM_ID";
const RPC_URL: &str = "https://api.devnet.solana.com";
/// Absolute path to the `instruction_data.bin` produced by `xark export solana`.
/// Contents: `proof_bytes (256 B) || public_inputs (N * 32 B)`.
const INSTRUCTION_DATA_PATH: &str = "/absolute/path/to/instruction_data.bin";
const PAYER_KEYPAIR_PATH: &str = "/absolute/path/to/payer.json";

fn main() -> Result<()> {
    let instruction_data = std::fs::read(INSTRUCTION_DATA_PATH)?;
    let program_id = Pubkey::from_str(PROGRAM_ID)?;
    let ix = Instruction {
        program_id,
        accounts: vec![],
        data: instruction_data,
    };
    let rpc = RpcClient::new_with_commitment(RPC_URL.to_string(), CommitmentConfig::confirmed());
    let payer = read_keypair_file(PAYER_KEYPAIR_PATH)
        .map_err(|e| anyhow::anyhow!("read keypair: {e}"))?;
    let blockhash = rpc.get_latest_blockhash()?;
    let tx =
        Transaction::new_signed_with_payer(&[ix], Some(&payer.pubkey()), &[&payer], blockhash);
    let sig = rpc.send_and_confirm_transaction(&tx)?;
    println!("Proof verified on-chain. Signature: {sig}");
    Ok(())
}
