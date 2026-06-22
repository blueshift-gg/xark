//! Pin the binary format of `verifying_key.bin`, `proof.bin`, and
//! `public_inputs.bin` for the `arithmetic_square` example.
//!
//! Downstream consumers (EVM verifier, Solana verifier) are going to read
//! these bytes directly, so the formats need to be frozen at this point. If
//! any future `ark-groth16` / `ark-serialize` bump silently changes the
//! on-disk layout, these tests will fail loudly.

use std::path::{Path, PathBuf};

use ark_bn254::Bn254;
use ark_groth16::{Proof, VerifyingKey};
use sha2::{Digest, Sha256};

use xark_backend::keys::Groth16Keys;
use xark_backend::proof::ProofBundle;
use xark_backend::serialization::read_public_inputs;

// Last bumped: Noir v1.0.0-beta.21 → v1.0.0-beta.22 (acir crate changes
// to `EmbeddedCurveAdd` / `MultiScalarMul` shift witness layout for every
// circuit, so the regenerated VK + proof bytes change too).
const VK_SHA256: &str = "0f197c9b98a5237e3d7d128d3653fe8f15f168f2046a16d7e978200f6d6eefbb";
const PROOF_SHA256: &str = "fbe4f937d8b1a073a3b3e312dd25de904610a0d627b885e892a50f0b7b2a4b9f";
const PUBLIC_INPUTS_BIN_SHA256: &str =
    "fed364fe00a941d1413ba656bed1e780117eac7beff4792ee33f6d02dab87798";

fn fixture_dir() -> PathBuf {
    // CARGO_MANIFEST_DIR = crates/tests; fixtures live alongside the crate at
    // crates/tests/fixtures/groth16/arithmetic_square/.
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("fixtures")
        .join("groth16")
        .join("arithmetic_square")
}

fn sha256_hex(path: &Path) -> String {
    let bytes = std::fs::read(path).expect("read fixture");
    let digest = Sha256::digest(&bytes);
    hex::encode(digest)
}

#[test]
fn vk_bytes_match_hash() {
    let actual = sha256_hex(&fixture_dir().join("verifying_key.bin"));
    assert_eq!(
        actual, VK_SHA256,
        "verifying_key.bin sha256 changed: actual={actual}"
    );
}

#[test]
fn proof_bytes_match_hash() {
    let actual = sha256_hex(&fixture_dir().join("proof.bin"));
    assert_eq!(
        actual, PROOF_SHA256,
        "proof.bin sha256 changed: actual={actual}"
    );
}

#[test]
fn vk_roundtrip() {
    let vk_path = fixture_dir().join("verifying_key.bin");
    let original_bytes = std::fs::read(&vk_path).expect("read vk");

    let vk: VerifyingKey<Bn254> = Groth16Keys::read_verifying_key(&vk_path).expect("parse vk");

    let tmp = unique_tempdir();
    let out_path = tmp.path().join("vk_roundtrip.bin");
    let keys = Groth16Keys {
        // The proving key is irrelevant here; reuse the parsed verifying key
        // through a throwaway bundle by going via the file helper directly.
        proving_key: ark_groth16::ProvingKey {
            vk: vk.clone(),
            beta_g1: ark_bn254::G1Affine::default(),
            delta_g1: ark_bn254::G1Affine::default(),
            a_query: vec![],
            b_g1_query: vec![],
            b_g2_query: vec![],
            h_query: vec![],
            l_query: vec![],
        },
        verifying_key: vk,
    };
    keys.write_verifying_key(&out_path).expect("write vk");
    let written = std::fs::read(&out_path).expect("read written vk");

    assert_eq!(
        written, original_bytes,
        "verifying_key.bin is not canonical: re-serialized bytes differ from the committed fixture"
    );
}

#[test]
fn proof_roundtrip() {
    let proof_path = fixture_dir().join("proof.bin");
    let original_bytes = std::fs::read(&proof_path).expect("read proof");

    let proof: Proof<Bn254> = ProofBundle::read_proof(&proof_path).expect("parse proof");

    let tmp = unique_tempdir();
    let out_path = tmp.path().join("proof_roundtrip.bin");
    let bundle = ProofBundle {
        proof,
        public_inputs: vec![],
    };
    bundle.write_proof(&out_path).expect("write proof");
    let written = std::fs::read(&out_path).expect("read written proof");

    assert_eq!(
        written, original_bytes,
        "proof.bin is not canonical: re-serialized bytes differ from the committed fixture"
    );
}

#[test]
fn end_to_end_verify_from_fixtures() {
    let dir = fixture_dir();
    let vk: VerifyingKey<Bn254> =
        Groth16Keys::read_verifying_key(&dir.join("verifying_key.bin")).expect("parse vk");
    let proof: Proof<Bn254> = ProofBundle::read_proof(&dir.join("proof.bin")).expect("parse proof");

    let public_inputs =
        read_public_inputs(&dir.join("public_inputs.bin")).expect("read public inputs");

    let ok = xark_backend::verify(&vk, &proof, &public_inputs).expect("verify");
    assert!(
        ok,
        "committed Groth16 fixtures failed to verify end-to-end against `xark_backend::verify`"
    );
}

// -- tiny tempdir helper (mirrors xark-cli/tests/end_to_end.rs to avoid a dep) -

struct TempDir {
    path: PathBuf,
}

impl TempDir {
    fn path(&self) -> &Path {
        &self.path
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.path);
    }
}

fn unique_tempdir() -> TempDir {
    use std::sync::atomic::{AtomicUsize, Ordering};
    static COUNTER: AtomicUsize = AtomicUsize::new(0);
    let n = COUNTER.fetch_add(1, Ordering::SeqCst);
    let pid = std::process::id();
    let path = std::env::temp_dir().join(format!("xark-a5-{pid}-{n}"));
    std::fs::create_dir_all(&path).expect("mkdir tempdir");
    TempDir { path }
}

#[test]
fn public_inputs_bytes_match_hash() {
    let actual = sha256_hex(&fixture_dir().join("public_inputs.bin"));
    assert_eq!(
        actual, PUBLIC_INPUTS_BIN_SHA256,
        "public_inputs.bin sha256 changed: actual={actual}"
    );
}
