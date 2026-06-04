//! `xark export solana` — emit the on-chain wire bytes for the
//! macro-generated Solana verifier program.
//!
//! Produces four files under `--out`:
//!
//! * `verifying_key.solana.bin` — LE-encoded VK, ready to drop into
//!   `xark_solana_verifier::xark_groth16_program! { vk: include_bytes!(...) }`.
//! * `proof.solana.bin` — `-A || B || C` (256 B, `A` pre-negated, LE Fq).
//! * `public_inputs.solana.bin` — `num_inputs * 32 B`, each Fr LE.
//! * `instruction_data.bin` — `proof_bytes || public_inputs`, the literal
//!   byte string a Solana client submits. The VK is *not* included
//!   because the on-chain program embeds it at compile time via the
//!   `xark_groth16_program!` macro.
//! * `client_call_example.rs` — copy-pasteable Solana client snippet.
//!
//! All field elements are 32-byte little-endian (the new
//! `solana-bn254 3.x` `alt_bn128_*_le` syscalls). Pass `--endianness be`
//! if you need the legacy big-endian wire format for an on-chain program
//! that hasn't migrated yet.

use std::fs;
use std::path::Path;

use anyhow::{Context, Result};
use clap::{Args, ValueEnum};

use groth16_backend::keys::Groth16Keys;
use groth16_backend::proof::ProofBundle;
use groth16_backend::serialization::PublicInputsJson;
use groth16_backend::solana::{
    assemble_proof_bytes_le, assemble_public_inputs_bytes_le, assemble_vk_bytes_le, encode_fr,
    encode_g1, encode_g2, negate_g1,
};

#[derive(Args, Debug)]
pub struct SolanaArgs {
    /// Path to the verifying key (canonical Arkworks binary format).
    #[arg(long)]
    pub verifying_key: std::path::PathBuf,
    /// Path to the proof (canonical Arkworks binary format).
    #[arg(long)]
    pub proof: std::path::PathBuf,
    /// Path to the public inputs JSON produced by `xark prove`.
    #[arg(long)]
    pub public_inputs: std::path::PathBuf,
    /// Directory to write the four Solana wire-format files into.
    #[arg(long)]
    pub out: std::path::PathBuf,
    /// Endianness of the produced files. Defaults to `le` to match the
    /// new on-chain verifier (`alt_bn128_*_le` syscalls); use `be` for
    /// the legacy Ethereum-compatible big-endian format if you maintain
    /// an older on-chain program.
    #[arg(long, value_enum, default_value_t = Endianness::Le)]
    pub endianness: Endianness,
}

#[derive(Clone, Copy, Debug, ValueEnum)]
pub enum Endianness {
    /// Little-endian (default; matches `alt_bn128_*_le` syscalls and
    /// `xark_solana_verifier::xark_groth16_program!`).
    Le,
    /// Big-endian (legacy Ethereum-compatible format).
    Be,
}

pub fn run(args: SolanaArgs) -> Result<()> {
    // ---- Load inputs ------------------------------------------------------
    let vk = Groth16Keys::read_verifying_key(&args.verifying_key)
        .with_context(|| format!("reading verifying key {}", args.verifying_key.display()))?;
    let proof = ProofBundle::read_proof(&args.proof)
        .with_context(|| format!("reading proof {}", args.proof.display()))?;
    let public_inputs_json_bytes = fs::read(&args.public_inputs)
        .with_context(|| format!("reading public inputs {}", args.public_inputs.display()))?;
    let public_inputs_json: PublicInputsJson = serde_json::from_slice(&public_inputs_json_bytes)
        .with_context(|| format!("parsing {}", args.public_inputs.display()))?;
    let public_inputs = public_inputs_json
        .into_fr()
        .with_context(|| format!("decoding {}", args.public_inputs.display()))?;

    let num_public_inputs = public_inputs.len();
    let ic_len = vk.gamma_abc_g1.len();
    if ic_len != num_public_inputs + 1 {
        anyhow::bail!(
            "VK ic length ({ic_len}) does not match num_public_inputs+1 ({}); \
             ic_len must equal num_public_inputs + 1 in Groth16",
            num_public_inputs + 1
        );
    }

    // ---- Encode ----------------------------------------------------------
    let (vk_bytes, proof_bytes, public_inputs_bytes) = match args.endianness {
        Endianness::Le => {
            let vk_bytes = assemble_vk_bytes_le(&vk);
            let proof_bytes = assemble_proof_bytes_le(&proof);
            let public_inputs_bytes = assemble_public_inputs_bytes_le(&public_inputs);
            (vk_bytes, proof_bytes, public_inputs_bytes)
        }
        Endianness::Be => {
            // Legacy BE path: ic_count is encoded big-endian. The
            // assembled bytes go to a program built before the
            // `alt_bn128_*_le` syscalls landed; keep it available so
            // users with pinned on-chain programs aren't stranded.
            let mut vk_bytes =
                Vec::with_capacity(64 + 3 * 128 + 4 + ic_len * 64);
            vk_bytes.extend_from_slice(&encode_g1(&vk.alpha_g1));
            vk_bytes.extend_from_slice(&encode_g2(&vk.beta_g2));
            vk_bytes.extend_from_slice(&encode_g2(&vk.gamma_g2));
            vk_bytes.extend_from_slice(&encode_g2(&vk.delta_g2));
            vk_bytes.extend_from_slice(&(ic_len as u32).to_be_bytes());
            for ic in &vk.gamma_abc_g1 {
                vk_bytes.extend_from_slice(&encode_g1(ic));
            }
            let mut proof_bytes = Vec::with_capacity(64 + 128 + 64);
            proof_bytes.extend_from_slice(&encode_g1(&negate_g1(&proof.a)));
            proof_bytes.extend_from_slice(&encode_g2(&proof.b));
            proof_bytes.extend_from_slice(&encode_g1(&proof.c));
            let mut public_inputs_bytes = Vec::with_capacity(public_inputs.len() * 32);
            for f in &public_inputs {
                public_inputs_bytes.extend_from_slice(&encode_fr(f));
            }
            (vk_bytes, proof_bytes, public_inputs_bytes)
        }
    };

    // ---- Assemble instruction data ---------------------------------------
    //
    // The new on-chain program embeds the VK at compile time via the
    // `xark_groth16_program!` macro, so the instruction data the client
    // submits is just `proof_bytes || public_inputs`. The VK file is
    // committed in the program crate's source tree and pulled in via
    // `include_bytes!`.
    let mut instruction_data = Vec::with_capacity(proof_bytes.len() + public_inputs_bytes.len());
    instruction_data.extend_from_slice(&proof_bytes);
    instruction_data.extend_from_slice(&public_inputs_bytes);

    // ---- Write outputs ----------------------------------------------------
    fs::create_dir_all(&args.out)
        .with_context(|| format!("creating output dir {}", args.out.display()))?;

    write_file(&args.out, "verifying_key.solana.bin", &vk_bytes)?;
    write_file(&args.out, "proof.solana.bin", &proof_bytes)?;
    write_file(&args.out, "public_inputs.solana.bin", &public_inputs_bytes)?;
    write_file(&args.out, "instruction_data.bin", &instruction_data)?;

    let example_path = args.out.join("client_call_example.rs");
    fs::write(&example_path, CLIENT_CALL_EXAMPLE)
        .with_context(|| format!("writing {}", example_path.display()))?;

    let endianness_label = match args.endianness {
        Endianness::Le => "little-endian",
        Endianness::Be => "big-endian",
    };
    println!(
        "Wrote {endianness_label} Solana wire-format export to {} ({} public input(s), \
         {} IC point(s), VK = {} B, instruction_data = {} B)",
        args.out.display(),
        num_public_inputs,
        ic_len,
        vk_bytes.len(),
        instruction_data.len()
    );
    Ok(())
}

fn write_file(dir: &Path, name: &str, bytes: &[u8]) -> Result<()> {
    let path = dir.join(name);
    fs::write(&path, bytes).with_context(|| format!("writing {}", path.display()))?;
    Ok(())
}

// -- Client snippet -----------------------------------------------------------

const CLIENT_CALL_EXAMPLE: &str = r#"//! Submit an xark-exported Groth16 proof to the on-chain verifier program.
//!
//! Workflow:
//!
//! 1. Embed `verifying_key.solana.bin` in your on-chain program crate
//!    via `xark_solana_verifier::xark_groth16_program! { vk: include_bytes!("vk.bin"), }`.
//! 2. Deploy the program (one program ID per VK).
//! 3. From the client, submit `instruction_data.bin` as the instruction
//!    data — just `proof_bytes || public_inputs`, no VK.
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
/// Absolute path to the `instruction_data.bin` produced by `xark export solana`.
/// Contents: `proof_bytes (256 B) || public_inputs (N * 32 B)`.
const INSTRUCTION_DATA_PATH: &str = "/absolute/path/to/instruction_data.bin";
const PAYER_KEYPAIR_PATH: &str = "/absolute/path/to/payer.json";

fn main() -> Result<()> {
    let instruction_data = std::fs::read(INSTRUCTION_DATA_PATH)?;
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
"#;
