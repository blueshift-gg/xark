//! Host-side (Arkworks-path) tests that need the committed fixtures. Moved
//! out of `xark-verifier`'s `#[cfg(test)]` modules so the verifier crate ships
//! no embedded test data. (Pure-logic unit tests with no fixtures — e.g. the
//! `scalar_is_canonical` boundary check — stay in the verifier crate.)

use xark_tests::{fixtures, verify_proof_only, VerifierError, FR_BYTES, PROOF_BYTES};

/// The committed KAT proof verifies via the host Arkworks path. The on-chain
/// (syscall) counterpart lives in `tests/sbpf.rs`.
#[test]
fn arithmetic_square_verifies() {
    let ok = verify_proof_only(
        fixtures::ARITHMETIC_SQUARE_VK_LE,
        fixtures::ARITHMETIC_SQUARE_INSTRUCTION_DATA,
    )
    .expect("structural validation");
    assert!(ok, "KAT proof should verify");
}

/// Flipping a public-input byte changes `vk_x`, so the pairing no longer
/// holds — `Ok(false)`, not an error (the point stays well-formed).
#[test]
fn tampered_public_input_rejected() {
    let mut data = fixtures::ARITHMETIC_SQUARE_INSTRUCTION_DATA.to_vec();
    data[PROOF_BYTES] ^= 0x01;
    let ok =
        verify_proof_only(fixtures::ARITHMETIC_SQUARE_VK_LE, &data).expect("structural validation");
    assert!(!ok, "tampered proof must not verify");
}

/// Truncated instruction data is rejected structurally, before any curve
/// arithmetic.
#[test]
fn truncated_instruction_data_rejected() {
    let short = &fixtures::ARITHMETIC_SQUARE_INSTRUCTION_DATA[..PROOF_BYTES - 1];
    assert!(matches!(
        verify_proof_only(fixtures::ARITHMETIC_SQUARE_VK_LE, short),
        Err(VerifierError::ProofLength { .. })
    ));
}

/// Regression for the public-input malleability: the committed
/// `arithmetic_square` input is `81`; `81 + r` is the same field element but a
/// non-canonical encoding. It used to verify (a different on-chain value under
/// the same proof) — it must now be rejected.
#[test]
fn non_canonical_public_input_rejected() {
    // 81 + r, little-endian.
    const PI_81_PLUS_R: [u8; FR_BYTES] = [
        0x52, 0x00, 0x00, 0xf0, 0x93, 0xf5, 0xe1, 0x43, 0x91, 0x70, 0xb9, 0x79, 0x48, 0xe8, 0x33,
        0x28, 0x5d, 0x58, 0x81, 0x81, 0xb6, 0x45, 0x50, 0xb8, 0x29, 0xa0, 0x31, 0xe1, 0x72, 0x4e,
        0x64, 0x30,
    ];
    let mut data = fixtures::ARITHMETIC_SQUARE_INSTRUCTION_DATA.to_vec();
    data[PROOF_BYTES..].copy_from_slice(&PI_81_PLUS_R);
    assert!(matches!(
        verify_proof_only(fixtures::ARITHMETIC_SQUARE_VK_LE, &data),
        Err(VerifierError::NonCanonicalPublicInput { index: 0 })
    ));
}

/// Typed path: the const-parsed `Verifier`/`Proof`/inputs verify (their very
/// existence exercises the `from_le_bytes` / `parse_public_inputs` compile-time
/// length checks).
#[test]
fn arithmetic_square_typed_verifies() {
    assert!(fixtures::ARITHMETIC_SQUARE_VK.verify(
        &fixtures::ARITHMETIC_SQUARE_PROOF,
        &fixtures::ARITHMETIC_SQUARE_INPUTS,
    ));
}

/// A flipped public-input bit breaks the typed pairing too.
#[test]
fn typed_tampered_input_rejected() {
    let mut inputs = fixtures::ARITHMETIC_SQUARE_INPUTS;
    inputs[0][0] ^= 0x01;
    assert!(!fixtures::ARITHMETIC_SQUARE_VK.verify(&fixtures::ARITHMETIC_SQUARE_PROOF, &inputs));
}
