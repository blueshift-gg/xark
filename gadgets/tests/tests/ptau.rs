//! Integration tests for the `.ptau` parser.
//!
//! These tests build a *minimal* valid Powers-of-Tau transcript in memory
//! (just `power = 1`, so the smallest legal one) using the same Montgomery
//! encoding snarkjs writes, then require the parser accepts it and reports
//! the correct structure. The negative-path tests then mutate this fixture
//! in targeted ways and require each mutation is caught with a specific
//! [`PtauError`] variant.
//!
//! We deliberately do **not** depend on a real snarkjs `.ptau` byte fixture
//! here — committing one of those would either (a) be tiny and synthetic
//! anyway (which is what this file already builds programmatically) or
//! (b) be hundreds of MiB, which is not appropriate for a unit-test
//! fixture. A future test will exercise a real Hermez transcript.

use ark_bn254::{Fr, G1Affine, G2Affine};
use ark_ec::AffineRepr;
use ark_ff::UniformRand;
use ark_std::rand::SeedableRng;
use rand_chacha::ChaCha20Rng;

use xark_backend::ptau::{parse_ptau, PtauError};

mod common;
use common::build_valid_ptau;

// ---- happy-path test --------------------------------------------------------

#[test]
fn parses_valid_minimal_ptau() {
    let bytes = build_valid_ptau(1);
    let parsed = parse_ptau(&bytes).expect("parse should succeed");

    assert_eq!(parsed.power, 1);
    // 2*2^1 - 1 = 3
    assert_eq!(parsed.tau_g1.len(), 3);
    // 2^1 = 2
    assert_eq!(parsed.tau_g2.len(), 2);
    assert_eq!(parsed.alpha_tau_g1.len(), 2);
    assert_eq!(parsed.beta_tau_g1.len(), 2);

    // tau_g1[0] must be G1 generator (= [τ^0]G1).
    assert_eq!(parsed.tau_g1[0], G1Affine::generator());
    // tau_g2[0] must be G2 generator.
    assert_eq!(parsed.tau_g2[0], G2Affine::generator());
    // All points must lie on the curve.
    assert!(parsed.tau_g1.iter().all(|p| p.is_on_curve()));
    assert!(parsed.tau_g2.iter().all(|p| p.is_on_curve()));
    assert!(parsed.alpha_tau_g1.iter().all(|p| p.is_on_curve()));
    assert!(parsed.beta_tau_g1.iter().all(|p| p.is_on_curve()));
    assert!(parsed.beta_g2.is_on_curve());
    // G2 subgroup membership.
    assert!(parsed
        .tau_g2
        .iter()
        .all(|p| p.is_in_correct_subgroup_assuming_on_curve()));
    assert!(parsed.beta_g2.is_in_correct_subgroup_assuming_on_curve());
}

#[test]
fn parses_valid_power_two_ptau() {
    // Slightly bigger to exercise non-trivial section sizes.
    let bytes = build_valid_ptau(2);
    let parsed = parse_ptau(&bytes).expect("parse should succeed");

    assert_eq!(parsed.power, 2);
    assert_eq!(parsed.tau_g1.len(), 2 * 4 - 1);
    assert_eq!(parsed.tau_g2.len(), 4);
    assert_eq!(parsed.alpha_tau_g1.len(), 4);
    assert_eq!(parsed.beta_tau_g1.len(), 4);
}

// ---- negative-path tests ----------------------------------------------------

#[test]
fn rejects_wrong_magic() {
    let mut bytes = build_valid_ptau(1);
    bytes[0..4].copy_from_slice(b"PTAU"); // wrong case
    match parse_ptau(&bytes) {
        Err(PtauError::BadMagic(b)) => assert_eq!(&b, b"PTAU"),
        other => panic!("expected BadMagic, got {other:?}"),
    }
}

#[test]
fn rejects_unsupported_version() {
    let mut bytes = build_valid_ptau(1);
    bytes[4..8].copy_from_slice(&999u32.to_le_bytes());
    match parse_ptau(&bytes) {
        Err(PtauError::UnsupportedVersion(v)) => assert_eq!(v, 999),
        other => panic!("expected UnsupportedVersion, got {other:?}"),
    }
}

#[test]
fn rejects_wrong_modulus() {
    // Re-serialize a fresh fixture but flip a bit in the header's modulus
    // field. The header begins immediately after the 4+4+4=12-byte file
    // prelude, then 4(ty) + 8(size) + 4(n8) = 16 more bytes; so the modulus
    // starts at offset 28.
    let mut bytes = build_valid_ptau(1);
    bytes[28] ^= 0x01;
    match parse_ptau(&bytes) {
        Err(PtauError::WrongCurve) => {}
        other => panic!("expected WrongCurve, got {other:?}"),
    }
}

#[test]
fn rejects_truncated_section() {
    let bytes = build_valid_ptau(1);
    // Lop off the last 100 bytes. The contributions section is the last
    // one and has size 0, so 100 bytes earlier puts us mid-beta_g2 (which
    // is 128 bytes long) or mid-beta_tau_g1.
    let truncated = &bytes[..bytes.len() - 100];
    match parse_ptau(truncated) {
        Err(PtauError::Truncated { .. }) => {}
        other => panic!("expected Truncated, got {other:?}"),
    }
}

#[test]
fn rejects_section_with_wrong_size() {
    // Craft a ptau where the tau_g1 section claims 3 points (correct for
    // power=1) but only has bytes for 2. We do this by manually building a
    // bad header byte stream.
    let mut bytes = build_valid_ptau(1);
    // Locate section 2's size field. Header start: offset 12 (prelude). The
    // header section's size field is at offset 12+4=16. Its payload is
    // (4 + 32 + 4 + 4) = 44 bytes. So section 2's type field starts at
    // 12 + 4 + 8 + 44 = 68. Its size field is at 68 + 4 = 72.
    let section2_size_off = 12 + 4 + 8 + 44 + 4;
    let original_size = u64::from_le_bytes(
        bytes[section2_size_off..section2_size_off + 8]
            .try_into()
            .unwrap(),
    );
    // Lie: claim the section is 64 bytes smaller (so we'd "lose" a point).
    let lied = original_size - 64;
    bytes[section2_size_off..section2_size_off + 8].copy_from_slice(&lied.to_le_bytes());

    // Re-parse: the size we declare now mismatches the count derived from
    // power, so we expect BadSectionSize.
    match parse_ptau(&bytes) {
        Err(PtauError::BadSectionSize { ty: 2, .. }) => {}
        // It is also legal for the parser to detect this as Truncated since
        // the *next* section's header lands at a different offset and may
        // run past EOF; both are valid rejections of a malformed file.
        Err(PtauError::Truncated { .. }) => {}
        other => panic!("expected BadSectionSize or Truncated, got {other:?}"),
    }
}

#[test]
fn rejects_missing_required_section() {
    // Build a transcript that simply omits the tau_g2 section. Easiest way:
    // re-serialize without it.
    let mut rng = ChaCha20Rng::seed_from_u64(7);
    let _ = Fr::rand(&mut rng); // burn for determinism stability

    let bytes_full = build_valid_ptau(1);
    // Strip section 3 (tau_g2) by walking sections and rebuilding.
    let stripped = strip_section(&bytes_full, 3);
    match parse_ptau(&stripped) {
        Err(PtauError::MissingSection(3, "tau_g2")) => {}
        other => panic!("expected MissingSection(3), got {other:?}"),
    }
}

#[test]
fn rejects_off_curve_point() {
    // Take a valid file and corrupt the *y* coordinate of the first
    // tau_g1 point so the point lies off-curve. The corruption needs to
    // produce a still-valid Mont-encoded Fq (which it will, since any
    // 32 bytes < p are valid).
    let mut bytes = build_valid_ptau(1);
    // Section 2 (tau_g1) payload starts after the header section. Header
    // section size = 44 bytes; section 2's payload starts at 12 + 4 + 8 +
    // 44 + 4 + 8 = 80. First G1 point = 64 bytes. We flip the second half
    // (y coordinate) at offset 80 + 32 = 112.
    let y_off = 12 + 4 + 8 + 44 + 4 + 8 + 32;
    bytes[y_off] ^= 0x01;
    match parse_ptau(&bytes) {
        Err(PtauError::InvalidPoint {
            section: "tau_g1",
            index: 0,
            ..
        }) => {}
        other => panic!("expected InvalidPoint in tau_g1[0], got {other:?}"),
    }
}

// ---- helpers ----------------------------------------------------------------

fn strip_section(bytes: &[u8], target_ty: u32) -> Vec<u8> {
    // 12-byte prelude.
    let mut out = Vec::with_capacity(bytes.len());
    out.extend_from_slice(&bytes[0..4]); // magic
    out.extend_from_slice(&bytes[4..8]); // version
    let num_sections = u32::from_le_bytes(bytes[8..12].try_into().unwrap());

    let mut cursor = 12;
    let mut kept_sections: Vec<&[u8]> = Vec::new();
    let mut kept_count: u32 = 0;
    for _ in 0..num_sections {
        let start = cursor;
        let ty = u32::from_le_bytes(bytes[cursor..cursor + 4].try_into().unwrap());
        cursor += 4;
        let size = u64::from_le_bytes(bytes[cursor..cursor + 8].try_into().unwrap()) as usize;
        cursor += 8;
        let end = cursor + size;
        if ty != target_ty {
            kept_sections.push(&bytes[start..end]);
            kept_count += 1;
        }
        cursor = end;
    }
    out.extend_from_slice(&kept_count.to_le_bytes());
    for s in kept_sections {
        out.extend_from_slice(s);
    }
    out
}
