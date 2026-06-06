//! Public-input binding sweep — the end-to-end soundness gate.
//!
//! The `#[svm_test]`s prove the *correct* statement verifies (completeness).
//! This asserts the complementary, soundness-relevant property: every public
//! input/output is *cryptographically bound* by the proof. For each committed
//! circuit it verifies the real fixtures, then flips one byte of each public
//! input in turn and asserts verification now **fails**. A public input that
//! could be changed while the proof still verified would be unbound —
//! forgeable by whoever submits the transaction.
//!
//! Unlike the constraint-matrix view (`xark-backend/tests/soundness.rs`),
//! this catches binding regardless of *how* an input is bound: Groth16 binds
//! every public input through the verifying key's IC (`gamma_abc`) elements,
//! even ones that appear in no constraint, so only an end-to-end check like
//! this is trustworthy. It runs on the host Arkworks path of the verifier, so
//! it's fast and needs no SBF toolchain.

use std::path::PathBuf;

use xark_tests::verify_groth16;

mod common;

fn circuit_dir(name: &str) -> PathBuf {
    common::groth16_fixture_dir().join(name)
}

const CIRCUITS: &[&str] = &[
    "arithmetic_square",
    "arithmetic_public_inputs",
    "bitwise_basic",
    "curve_basic",
    "mixed_pi",
    "reorder_pi",
    "range_basic",
    "memory_const",
    "memory_var",
    "multi_function",
    "nested_calls",
    "return_values_only",
    "brillig_basic",
    "poseidon_basic",
    "large_pi",
    "sha256_basic",
    "keccak_basic",
    "aes128_basic",
    "blake2s_basic",
    "blake3_basic",
    "ecdsa_basic",
    "ecdsa_r1_basic",
];

#[test]
fn every_public_input_is_bound() {
    for name in CIRCUITS {
        let dir = circuit_dir(name);
        let vk = std::fs::read(dir.join("verifying_key.solana.bin")).expect("read vk");
        let proof = std::fs::read(dir.join("proof.solana.bin")).expect("read proof");
        let inputs = std::fs::read(dir.join("public_inputs.solana.bin")).expect("read inputs");
        assert_eq!(
            inputs.len() % 32,
            0,
            "{name}: public inputs not a multiple of 32"
        );
        let n = inputs.len() / 32;

        // Baseline: the committed fixtures verify.
        assert!(
            verify_groth16(&vk, &proof, &inputs).expect("verify"),
            "{name}: committed fixtures must verify"
        );

        // Each public input must be bound: flipping its low byte (a ±1 change
        // to the scalar, always a distinct residue mod r) must break the proof.
        for i in 0..n {
            let mut tampered = inputs.clone();
            tampered[i * 32] ^= 0x01;
            // `unwrap_or(false)`: a failed pairing (`Ok(false)`) and a rejected
            // input (`Err`, e.g. a flip that lands on a non-canonical value)
            // both mean "bound".
            let still_ok = verify_groth16(&vk, &proof, &tampered).unwrap_or(false);
            assert!(
                !still_ok,
                "{name}: flipping public input #{i} still verified — it is UNBOUND (forgeable)"
            );
        }

        eprintln!("{name}: {n} public input(s), all bound");
    }
}
