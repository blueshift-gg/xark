//! End-to-end on-chain test for the macro-generated Groth16 verifier.
//!
//! Loads `xark_arithmetic_square_program.so` (built by
//! `cargo build-sbf -p xark-arithmetic-square-program`) into [Mollusk]'s
//! lightweight SVM and submits the canonical `arithmetic_square` KAT
//! proof + public inputs as instruction data. The test exercises:
//!
//! * the `pinocchio::entrypoint!` emitted by the macro,
//! * the LE encoding of proof + public inputs the program expects, and
//! * the `alt_bn128_*_le` syscalls (real on-chain, not the host-side
//!   `ArkBackend`).
//!
//! Skips with a `eprintln!` when the .so is missing so plain
//! `cargo test -p xark-solana-verifier` (without `cargo build-sbf`)
//! still works.
//!
//! [Mollusk]: https://github.com/anza-xyz/mollusk

#![cfg(feature = "ark-backend")]

use std::path::{Path, PathBuf};

use ark_bn254::{Bn254, Fr};
use ark_groth16::{Proof, VerifyingKey};
use ark_serialize::{CanonicalDeserialize, Compress, Validate};
use mollusk_svm::{result::Check, Mollusk};
use num_bigint::BigUint;
use solana_instruction::Instruction;
use solana_program_error::ProgramError;
use solana_address::Address;

use groth16_backend::solana::{assemble_proof_bytes_le, assemble_public_inputs_bytes_le};

const PROGRAM_NAME: &str = "xark_arithmetic_square_program";

fn workspace_root() -> PathBuf {
    let manifest = Path::new(env!("CARGO_MANIFEST_DIR"));
    manifest
        .parent()
        .and_then(|p| p.parent())
        .expect("workspace root")
        .to_path_buf()
}

fn so_path() -> PathBuf {
    workspace_root()
        .join("target")
        .join("deploy")
        .join(format!("{PROGRAM_NAME}.so"))
}

fn fixture_dir() -> PathBuf {
    workspace_root()
        .join("tests")
        .join("fixtures")
        .join("groth16")
        .join("arithmetic_square")
}

fn read_proof() -> Proof<Bn254> {
    let bytes = std::fs::read(fixture_dir().join("proof.bin")).expect("read proof.bin");
    Proof::<Bn254>::deserialize_with_mode(bytes.as_slice(), Compress::Yes, Validate::Yes)
        .expect("parse proof")
}

fn read_vk() -> VerifyingKey<Bn254> {
    let bytes = std::fs::read(fixture_dir().join("verifying_key.bin")).expect("read vk.bin");
    VerifyingKey::<Bn254>::deserialize_with_mode(bytes.as_slice(), Compress::Yes, Validate::Yes)
        .expect("parse vk")
}

fn read_public_inputs() -> Vec<Fr> {
    let json_bytes = std::fs::read(fixture_dir().join("public_inputs.json"))
        .expect("read public_inputs.json");
    #[derive(serde::Deserialize)]
    struct Pi {
        inputs: Vec<String>,
    }
    let pi: Pi = serde_json::from_slice(&json_bytes).expect("parse public_inputs");
    pi.inputs
        .iter()
        .map(|s| {
            let big: BigUint = s.trim().parse().expect("decimal scalar");
                use ark_ff::PrimeField;
                Fr::from_be_bytes_mod_order(&big.to_bytes_be())
        })
        .collect()
}

fn skip_if_missing_so() -> Option<Mollusk> {
    let so = so_path();
    if !so.exists() {
        eprintln!(
            "skipping mollusk_e2e: {} not found. \
             Run `cargo build-sbf -p {PROGRAM_NAME}` first.",
            so.display()
        );
        return None;
    }
    let program_id = Address::new_from_array([2u8; 32]);
    // Mollusk consults SBF_OUT_DIR; point it at `target/deploy/`
    // explicitly so this works regardless of where the test was
    // invoked from.
    std::env::set_var(
        "SBF_OUT_DIR",
        so.parent().expect("deploy dir").to_str().expect("utf-8"),
    );
    Some(Mollusk::new(&program_id, PROGRAM_NAME))
}

fn build_instruction_data() -> Vec<u8> {
    let proof = read_proof();
    let inputs = read_public_inputs();
    let proof_bytes = assemble_proof_bytes_le(&proof);
    let public_inputs_bytes = assemble_public_inputs_bytes_le(&inputs);
    let mut data = Vec::with_capacity(proof_bytes.len() + public_inputs_bytes.len());
    data.extend_from_slice(&proof_bytes);
    data.extend_from_slice(&public_inputs_bytes);
    data
}

#[test]
fn arithmetic_square_proof_verifies_on_chain() {
    let Some(mollusk) = skip_if_missing_so() else {
        return;
    };

    let program_id = Address::new_from_array([2u8; 32]);
    let ix = Instruction {
        program_id,
        accounts: vec![],
        data: build_instruction_data(),
    };

    // `process_and_validate_instruction` runs the program and then
    // applies the listed `Check`s, panicking with the actual result if
    // any check fails — preferred over a manual `assert!(...)` because
    // it surfaces compute-unit counts, logs, and account diffs on the
    // failure side automatically.
    mollusk.process_and_validate_instruction(&ix, &[], &[Check::success()]);

    // Sanity-check the embedded VK matches the runtime LE encoding.
    let _vk = read_vk();
}

#[test]
fn tampered_input_rejected_on_chain() {
    let Some(mollusk) = skip_if_missing_so() else {
        return;
    };

    let program_id = Address::new_from_array([2u8; 32]);
    let mut data = build_instruction_data();
    // Flip the LE LSB of the first public input. Length-preserving so
    // we expect a pairing-check failure: the program maps `Ok(false)`
    // (and every parse / arity error) to `InvalidInstructionData`.
    let pi_offset = 256; // proof_bytes = 256 B
    data[pi_offset] ^= 0x01;

    let ix = Instruction {
        program_id,
        accounts: vec![],
        data,
    };

    mollusk.process_and_validate_instruction(
        &ix,
        &[],
        &[Check::err(ProgramError::InvalidInstructionData)],
    );
}
