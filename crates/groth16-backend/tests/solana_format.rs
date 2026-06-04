//! Pin the on-chain (Solana / Ethereum `alt_bn128`) byte layout of the
//! committed `verifying_key.bin` and `proof.bin` fixtures for the
//! `arithmetic_square` example.
//!
//! These hashes serve as a fingerprint of the on-chain format. Any change
//! to the encoding helpers in `groth16_backend::solana` or to the way the
//! prover constructs VK / proof points will trip these tests loudly, so the
//! downstream Solana verifier (E.2.b) can rely on a stable wire format.

use std::path::{Path, PathBuf};

use sha2::{Digest, Sha256};

use groth16_backend::keys::Groth16Keys;
use groth16_backend::proof::ProofBundle;
use groth16_backend::solana::{encode_g1, encode_g2, negate_g1};

const VK_SOLANA_SHA256: &str = "099bb4408828730ff40a51738ff002b18366f2fa5f88c29352b6d54437aee9f1";
const PROOF_SOLANA_SHA256: &str =
    "f083fb2047ff5a8f354668a2bafe09abd75c839f5998c45a965c9d93461fcb71";
const PROOF_NEG_A_SOLANA_SHA256: &str =
    "8617e4a7e90dabab4c315b2522f1094fc7d6c0267e58e28ebec546fca68f4336";

fn fixture_dir() -> PathBuf {
    let manifest = Path::new(env!("CARGO_MANIFEST_DIR"));
    manifest
        .parent()
        .and_then(|p| p.parent())
        .expect("workspace root")
        .join("tests")
        .join("fixtures")
        .join("groth16")
        .join("arithmetic_square")
}

fn sha256_hex(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    hex::encode(digest)
}

/// Encode the verifying key into the Solana on-chain format:
/// `alpha_g1 || beta_g2 || gamma_g2 || delta_g2 || ic[0] || ic[1] || ...`.
fn encode_vk_solana(vk: &ark_groth16::VerifyingKey<ark_bn254::Bn254>) -> Vec<u8> {
    let mut out = Vec::new();
    out.extend_from_slice(&encode_g1(&vk.alpha_g1));
    out.extend_from_slice(&encode_g2(&vk.beta_g2));
    out.extend_from_slice(&encode_g2(&vk.gamma_g2));
    out.extend_from_slice(&encode_g2(&vk.delta_g2));
    for ic in &vk.gamma_abc_g1 {
        out.extend_from_slice(&encode_g1(ic));
    }
    out
}

/// Encode a proof into the Solana on-chain format: `A || B || C`.
fn encode_proof_solana(proof: &ark_groth16::Proof<ark_bn254::Bn254>) -> Vec<u8> {
    let mut out = Vec::with_capacity(64 + 128 + 64);
    out.extend_from_slice(&encode_g1(&proof.a));
    out.extend_from_slice(&encode_g2(&proof.b));
    out.extend_from_slice(&encode_g1(&proof.c));
    out
}

/// Same as `encode_proof_solana`, but with `A` already negated so the
/// on-chain code can drop it straight into the pairing input.
fn encode_proof_solana_negated_a(proof: &ark_groth16::Proof<ark_bn254::Bn254>) -> Vec<u8> {
    let mut out = Vec::with_capacity(64 + 128 + 64);
    out.extend_from_slice(&encode_g1(&negate_g1(&proof.a)));
    out.extend_from_slice(&encode_g2(&proof.b));
    out.extend_from_slice(&encode_g1(&proof.c));
    out
}

#[test]
fn vk_solana_bytes_match_hash() {
    let vk = Groth16Keys::read_verifying_key(&fixture_dir().join("verifying_key.bin"))
        .expect("parse vk");
    let bytes = encode_vk_solana(&vk);
    // arithmetic_square has 2 public IC entries, so the VK is
    // 64 (alpha) + 3*128 (beta/gamma/delta) + 2*64 (ic) = 576 bytes.
    let expected_len = 64 + 3 * 128 + vk.gamma_abc_g1.len() * 64;
    assert_eq!(bytes.len(), expected_len, "unexpected VK encoding length");

    let actual = sha256_hex(&bytes);
    assert_eq!(
        actual,
        VK_SOLANA_SHA256,
        "Solana-format VK bytes changed: actual={actual}, len={}",
        bytes.len()
    );
}

#[test]
fn proof_solana_bytes_match_hash() {
    let proof = ProofBundle::read_proof(&fixture_dir().join("proof.bin")).expect("parse proof");
    let bytes = encode_proof_solana(&proof);
    assert_eq!(bytes.len(), 64 + 128 + 64, "proof must be 256 bytes");

    let actual = sha256_hex(&bytes);
    assert_eq!(
        actual, PROOF_SOLANA_SHA256,
        "Solana-format proof bytes changed: actual={actual}"
    );
}

#[test]
fn proof_solana_neg_a_bytes_match_hash() {
    let proof = ProofBundle::read_proof(&fixture_dir().join("proof.bin")).expect("parse proof");
    let bytes = encode_proof_solana_negated_a(&proof);
    assert_eq!(
        bytes.len(),
        64 + 128 + 64,
        "proof (negated-A) must be 256 bytes"
    );

    let actual = sha256_hex(&bytes);
    assert_eq!(
        actual, PROOF_NEG_A_SOLANA_SHA256,
        "Solana-format proof bytes (with negated A) changed: actual={actual}"
    );

    // Sanity: negating twice must reproduce the original A bytes.
    let twice = encode_g1(&negate_g1(&negate_g1(&proof.a)));
    assert_eq!(twice, encode_g1(&proof.a));
}
