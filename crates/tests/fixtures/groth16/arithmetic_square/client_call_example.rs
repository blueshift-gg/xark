//! Submit an xark-exported Groth16 proof to your on-chain verifier program.
//!
//! Your program embeds the verifying key via the generated verifier crate
//! (`<crate>::verify_instruction_data(...)`); the client just submits
//! `instruction_data.bin` (= `proof_bytes || public_inputs`, no VK).
//!
//! Uses Anza's broken-out client crates rather than the monolithic
//! `solana-sdk`. Copy this file into a fresh Cargo project with:
//!
//! ```toml
//! [dependencies]
//! anyhow = "1"
//! solana-address = "2"
//! solana-client = "2"
//! solana-commitment-config = "3"
//! solana-instruction = "3"
//! solana-keypair = "3"
//! solana-message = "3"
//! solana-signer = "3"
//! solana-transaction = "3"
//! ```

use std::str::FromStr;

use anyhow::Result;
use solana_address::Address;
use solana_client::rpc_client::RpcClient;
use solana_commitment_config::CommitmentConfig;
use solana_instruction::Instruction;
use solana_keypair::read_keypair_file;
use solana_signer::Signer;
use solana_transaction::Transaction;

// ---- Fill these in ---------------------------------------------------------
const PROGRAM_ID: &str = "REPLACE_WITH_DEPLOYED_PROGRAM_ID";
const RPC_URL: &str = "https://api.devnet.solana.com";
/// Absolute path to the `instruction_data.bin` produced by `xark export`.
/// Contents: `proof_bytes (256 B) || public_inputs (N * 32 B)`.
const INSTRUCTION_DATA_PATH: &str = "/absolute/path/to/instruction_data.bin";
const PAYER_KEYPAIR_PATH: &str = "/absolute/path/to/payer.json";

fn main() -> Result<()> {
 let instruction_data = std::fs::read(INSTRUCTION_DATA_PATH)?;
 // If your program uses a discriminator, prefix the instruction data with it:
 //
 //   let mut data = Vec::with_capacity(1 + instruction_data.len());
 //   data.push(0x00);
 //   data.extend_from_slice(&instruction_data);
 //   let instruction_data = data;
 //
 let program_id = Address::from_str(PROGRAM_ID)?;
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
