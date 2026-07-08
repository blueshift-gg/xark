//! Pin the on-chain (Solana / Ethereum `alt_bn128`) byte layout of the
//! committed `verifying_key.bin` and `proof.bin` fixtures for the
//! `arithmetic_square` example.
//!
//! These hashes serve as a fingerprint of the on-chain format. Any change
//! to the encoding helpers in `xark_backend::solana` or to the way the
//! prover constructs VK / proof points will trip these tests loudly, so the
//! downstream Solana verifier (E.2.b) can rely on a stable wire format.

use std::path::{Path, PathBuf};

use sha2::{Digest, Sha256};

use xark_backend::keys::Groth16Keys;
use xark_backend::proof::ProofBundle;
use xark_backend::solana::{encode_g1, encode_g2, negate_g1};

// Bump when the Solana wire layout changes (regenerating the Groth16
// fixtures moves these digests). The pinned values are the test-computed sha256
// over `encode_vk_solana(vk)` / `encode_proof_solana(proof)` — these
// re-encode from the Arkworks verifying_key.bin / proof.bin files via
// the test's helpers, not over the `.solana.bin` files directly.
const VK_SOLANA_SHA256: &str = "822b76b129e52e2fbca61562e39260b7988474af66962a4a9ff6098c747e3963";
const PROOF_SOLANA_SHA256: &str =
    "246e7dd59354da00c0e7f50f9ea2c37befbe983700a5743ecafbbbd4e9463205";
const PROOF_NEG_A_SOLANA_SHA256: &str =
    "ca676ad7c3194c393348b8ac16c56a841e6b20191f7cbb452be1f4c829ef9c68";

fn fixture_dir() -> PathBuf {
    // CARGO_MANIFEST_DIR = crates/tests; fixtures live alongside the crate at
    // crates/tests/fixtures/groth16/arithmetic_square/.
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("fixtures")
        .join("groth16")
        .join("arithmetic_square")
}

fn sha256_hex(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    hex::encode(digest)
}

/// Encode the verifying key into the Solana on-chain format:
/// `alpha_g1 || beta_g2 || gamma_g2 || delta_g2 || ic[0] || ic[1] ||...`.
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
