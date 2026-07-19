//! On-chain (SBPF) tests + compute-unit benchmarks for the Groth16 verifier,
//! one per committed circuit.
//!
//! `svm-unit-test` compiles each `#[svm_test]` body into its own `no_std`
//! cdylib, loads it into Mollusk, and runs it on the real `alt_bn128`
//! syscalls. A failed verification trips the `assert`, which panics on chain
//! and fails the test — so each of these is a correctness check, and the
//! logged CU count is the real per-proof cost for that circuit's public-input
//! count `N` (the `vk_x` linear combination is `N` G1 muls + adds, on top of
//! the fixed 4-pair pairing).
//!
//! Each body must be a literal `#[svm_test] fn` — `svm-unit-test` discovers
//! them by parsing this source, so they can't be macro-generated.

use svm_unit_test::svm_test;
use xark_tests::{fixtures, verify_proof_only, verify_proof_only_strict};

/// Dynamic byte path: `verify_proof_only(vk_bytes, instruction_data)`.
#[svm_test]
fn arithmetic_square_bytes() {
    let ok = verify_proof_only(
        fixtures::ARITHMETIC_SQUARE_VK_LE,
        fixtures::ARITHMETIC_SQUARE_INSTRUCTION_DATA,
    )
    .unwrap();
    assert!(ok);
}

/// On-chain confirmation of the coordinate-encoding malleability and its
/// `*_strict` fix, run against the *real* `alt_bn128` syscall.
///
/// Byte 63 is the most-significant byte of `-A.y`; its top bit (bit 255 of the
/// 256-bit limb) is an unused flag bit the syscall **masks**. Flipping it
/// yields byte-distinct instruction data that decodes to the same point:
///   * the plain syscall path still verifies it (the malleability is real on
///     chain, not just on the host reference path), while
///   * `verify_proof_only_strict` rejects it (the canonical-encoding check).
#[svm_test]
fn flag_bit_mutation_onchain() {
    // arithmetic_square instruction data = 256-byte proof + 1 × 32-byte input.
    let mut data = [0u8; 256 + 32];
    data.copy_from_slice(fixtures::ARITHMETIC_SQUARE_INSTRUCTION_DATA);
    data[63] ^= 0x80; // flip the unused top flag bit of -A.y

    // Unmodified data still verifies under strict (sanity).
    assert!(verify_proof_only_strict(
        fixtures::ARITHMETIC_SQUARE_VK_LE,
        fixtures::ARITHMETIC_SQUARE_INSTRUCTION_DATA,
    )
    .unwrap());

    // Non-strict: the syscall masks the flag bit, so the mutated bytes verify.
    assert!(verify_proof_only(fixtures::ARITHMETIC_SQUARE_VK_LE, &data).unwrap());

    // Strict: the canonical-encoding check rejects the non-canonical coordinate.
    assert!(verify_proof_only_strict(fixtures::ARITHMETIC_SQUARE_VK_LE, &data).is_err());
}

// Typed path: `const VK: Verifier<N>` → `VK.verify(&PROOF, &INPUTS)`,
// one per circuit. `N` spans 0 (ecdsa) to 16 (aes128, large_pi).

#[svm_test]
fn arithmetic_square() {
    assert!(fixtures::ARITHMETIC_SQUARE_VK.verify(
        &fixtures::ARITHMETIC_SQUARE_PROOF,
        &fixtures::ARITHMETIC_SQUARE_INPUTS
    ));
}

#[svm_test]
fn aes128_basic() {
    assert!(fixtures::AES128_BASIC_VK.verify(
        &fixtures::AES128_BASIC_PROOF,
        &fixtures::AES128_BASIC_INPUTS
    ));
}

#[svm_test]
fn arithmetic_public_inputs() {
    assert!(fixtures::ARITHMETIC_PUBLIC_INPUTS_VK.verify(
        &fixtures::ARITHMETIC_PUBLIC_INPUTS_PROOF,
        &fixtures::ARITHMETIC_PUBLIC_INPUTS_INPUTS,
    ));
}

#[svm_test]
fn bitwise_basic() {
    assert!(fixtures::BITWISE_BASIC_VK.verify(
        &fixtures::BITWISE_BASIC_PROOF,
        &fixtures::BITWISE_BASIC_INPUTS
    ));
}

#[svm_test]
fn blake2s_basic() {
    assert!(fixtures::BLAKE2S_BASIC_VK.verify(
        &fixtures::BLAKE2S_BASIC_PROOF,
        &fixtures::BLAKE2S_BASIC_INPUTS
    ));
}

#[svm_test]
fn blake3_basic() {
    assert!(fixtures::BLAKE3_BASIC_VK.verify(
        &fixtures::BLAKE3_BASIC_PROOF,
        &fixtures::BLAKE3_BASIC_INPUTS
    ));
}

#[svm_test]
fn curve_basic() {
    assert!(fixtures::CURVE_BASIC_VK
        .verify(&fixtures::CURVE_BASIC_PROOF, &fixtures::CURVE_BASIC_INPUTS));
}

#[svm_test]
fn secp256k1_ecdsa() {
    assert!(fixtures::SECP256K1_ECDSA_VK.verify(
        &fixtures::SECP256K1_ECDSA_PROOF,
        &fixtures::SECP256K1_ECDSA_INPUTS
    ));
}

#[svm_test]
fn secp256r1_ecdsa() {
    assert!(fixtures::SECP256R1_ECDSA_VK.verify(
        &fixtures::SECP256R1_ECDSA_PROOF,
        &fixtures::SECP256R1_ECDSA_INPUTS
    ));
}

#[svm_test]
fn keccak_basic() {
    assert!(fixtures::KECCAK_BASIC_VK.verify(
        &fixtures::KECCAK_BASIC_PROOF,
        &fixtures::KECCAK_BASIC_INPUTS
    ));
}

#[svm_test]
fn large_pi() {
    assert!(fixtures::LARGE_PI_VK.verify(&fixtures::LARGE_PI_PROOF, &fixtures::LARGE_PI_INPUTS));
}

#[svm_test]
fn memory_const() {
    assert!(fixtures::MEMORY_CONST_VK.verify(
        &fixtures::MEMORY_CONST_PROOF,
        &fixtures::MEMORY_CONST_INPUTS
    ));
}

#[svm_test]
fn memory_var() {
    assert!(
        fixtures::MEMORY_VAR_VK.verify(&fixtures::MEMORY_VAR_PROOF, &fixtures::MEMORY_VAR_INPUTS)
    );
}

#[svm_test]
fn mixed_pi() {
    assert!(fixtures::MIXED_PI_VK.verify(&fixtures::MIXED_PI_PROOF, &fixtures::MIXED_PI_INPUTS));
}

#[svm_test]
fn multi_function() {
    assert!(fixtures::MULTI_FUNCTION_VK.verify(
        &fixtures::MULTI_FUNCTION_PROOF,
        &fixtures::MULTI_FUNCTION_INPUTS
    ));
}

#[svm_test]
fn nested_calls() {
    assert!(fixtures::NESTED_CALLS_VK.verify(
        &fixtures::NESTED_CALLS_PROOF,
        &fixtures::NESTED_CALLS_INPUTS
    ));
}

#[svm_test]
fn poseidon_basic() {
    assert!(fixtures::POSEIDON_BASIC_VK.verify(
        &fixtures::POSEIDON_BASIC_PROOF,
        &fixtures::POSEIDON_BASIC_INPUTS
    ));
}

#[svm_test]
fn range_basic() {
    assert!(fixtures::RANGE_BASIC_VK
        .verify(&fixtures::RANGE_BASIC_PROOF, &fixtures::RANGE_BASIC_INPUTS));
}

#[svm_test]
fn reorder_pi() {
    assert!(
        fixtures::REORDER_PI_VK.verify(&fixtures::REORDER_PI_PROOF, &fixtures::REORDER_PI_INPUTS)
    );
}

#[svm_test]
fn return_values_only() {
    assert!(fixtures::RETURN_VALUES_ONLY_VK.verify(
        &fixtures::RETURN_VALUES_ONLY_PROOF,
        &fixtures::RETURN_VALUES_ONLY_INPUTS
    ));
}

#[svm_test]
fn sha256_basic() {
    assert!(fixtures::SHA256_BASIC_VK.verify(
        &fixtures::SHA256_BASIC_PROOF,
        &fixtures::SHA256_BASIC_INPUTS
    ));
}

// ---- On-chain NEGATIVE tests: bad inputs must be REJECTED on chain ---------
//
// `assert!(!accepted)` — if the verifier wrongly ACCEPTS, the body panics, the
// program fails, and the test fails. So a green test means the input was
// rejected on chain (by the real syscalls), closing the gap that the host
// rejection tests can't cover. All operate on the `arithmetic_square` fixture
// (proof = 256 B, then one 32-B public input).

/// `81 + r` (LE): a non-canonical encoding of the committed public input `81`.
/// Reduces to the same field element, so without the canonical-scalar check it
/// would verify under the same proof (public-input malleability).
const ARITHMETIC_SQUARE_PI_PLUS_R: [u8; 32] = [
    0x52, 0x00, 0x00, 0xf0, 0x93, 0xf5, 0xe1, 0x43, 0x91, 0x70, 0xb9, 0x79, 0x48, 0xe8, 0x33, 0x28,
    0x5d, 0x58, 0x81, 0x81, 0xb6, 0x45, 0x50, 0xb8, 0x29, 0xa0, 0x31, 0xe1, 0x72, 0x4e, 0x64, 0x30,
];

#[svm_test]
fn reject_noncanonical_public_input() {
    let ix = fixtures::ARITHMETIC_SQUARE_INSTRUCTION_DATA;
    let mut data = [0u8; 288];
    data[..256].copy_from_slice(&ix[..256]);
    data[256..].copy_from_slice(&ARITHMETIC_SQUARE_PI_PLUS_R);
    assert!(!verify_proof_only(fixtures::ARITHMETIC_SQUARE_VK_LE, &data).unwrap_or(false));
}

#[svm_test]
fn reject_tampered_proof() {
    let ix = fixtures::ARITHMETIC_SQUARE_INSTRUCTION_DATA;
    let mut data = [0u8; 288];
    data.copy_from_slice(ix);
    data[0] ^= 0x01; // flip a bit in proof.A's x-coordinate
    assert!(!verify_proof_only(fixtures::ARITHMETIC_SQUARE_VK_LE, &data).unwrap_or(false));
}

#[svm_test]
fn reject_offcurve_proof_a() {
    let ix = fixtures::ARITHMETIC_SQUARE_INSTRUCTION_DATA;
    let mut data = [0u8; 288];
    data.copy_from_slice(ix);
    data[0] ^= 0xFF; // almost-certainly drives proof.A off-curve → syscall error
    data[1] ^= 0xFF;
    assert!(!verify_proof_only(fixtures::ARITHMETIC_SQUARE_VK_LE, &data).unwrap_or(false));
}

#[svm_test]
fn reject_truncated_instruction_data() {
    let ix = fixtures::ARITHMETIC_SQUARE_INSTRUCTION_DATA;
    assert!(!verify_proof_only(fixtures::ARITHMETIC_SQUARE_VK_LE, &ix[..200]).unwrap_or(false));
}
