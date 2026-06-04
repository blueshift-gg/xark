//! Integration tests for the `.ptau` parser.
//!
//! These tests build a *minimal* valid Powers-of-Tau transcript in memory
//! (just `power = 1`, so the smallest legal one) using the same Montgomery
//! encoding snarkjs writes, then assert the parser accepts it and reports
//! the correct structure. The negative-path tests then mutate this fixture
//! in targeted ways and assert each mutation is caught with a specific
//! [`PtauError`] variant.
//!
//! We deliberately do **not** depend on a real snarkjs `.ptau` byte fixture
//! here — committing one of those would either (a) be tiny and synthetic
//! anyway (which is what this file already builds programmatically) or
//! (b) be hundreds of MiB, which is not appropriate for a unit-test
//! fixture. A future test in WS-F.2 will exercise a real Hermez transcript.

use ark_bn254::{Fq, Fr, G1Affine, G2Affine};
use ark_ec::{AdditiveGroup, AffineRepr, CurveGroup, PrimeGroup};
use ark_ff::{BigInteger, Field, PrimeField, UniformRand};
use ark_std::rand::SeedableRng;
use rand_chacha::ChaCha20Rng;

use groth16_backend::ptau::{__fq_to_le_mont_bytes_for_tests as fq_to_mont, parse_ptau, PtauError};

// ---- fixture builders -------------------------------------------------------

/// Build a programmatic ptau file by sampling a τ, α, β ∈ Fr, computing the
/// expected powers, and serializing them in the snarkjs binary layout.
///
/// `power` is small (1 or 2 in tests) so the resulting buffer stays a few
/// kilobytes.
fn build_valid_ptau(power: u32) -> Vec<u8> {
    let mut rng = ChaCha20Rng::seed_from_u64(0x00C0_FFEE_F00D);
    let tau = Fr::rand(&mut rng);
    let alpha = Fr::rand(&mut rng);
    let beta = Fr::rand(&mut rng);

    let two_to_p = 1usize << power;
    let g1 = ark_bn254::G1Projective::generator();
    let g2 = ark_bn254::G2Projective::generator();

    // [τ^0]G1 ... [τ^(2·2^p - 2)]G1
    let n_tau_g1 = 2 * two_to_p - 1;
    let mut tau_g1 = Vec::with_capacity(n_tau_g1);
    let mut acc = Fr::ONE;
    for _ in 0..n_tau_g1 {
        tau_g1.push((g1 * acc).into_affine());
        acc *= tau;
    }

    // [τ^0]G2 ... [τ^(2^p - 1)]G2
    let mut tau_g2 = Vec::with_capacity(two_to_p);
    acc = Fr::ONE;
    for _ in 0..two_to_p {
        tau_g2.push((g2 * acc).into_affine());
        acc *= tau;
    }

    // [α·τ^i]G1
    let mut alpha_tau_g1 = Vec::with_capacity(two_to_p);
    acc = alpha;
    for _ in 0..two_to_p {
        alpha_tau_g1.push((g1 * acc).into_affine());
        acc *= tau;
    }

    // [β·τ^i]G1
    let mut beta_tau_g1 = Vec::with_capacity(two_to_p);
    acc = beta;
    for _ in 0..two_to_p {
        beta_tau_g1.push((g1 * acc).into_affine());
        acc *= tau;
    }

    let beta_g2 = (g2 * beta).into_affine();

    serialize_ptau(
        power,
        &tau_g1,
        &tau_g2,
        &alpha_tau_g1,
        &beta_tau_g1,
        &beta_g2,
    )
}

fn serialize_ptau(
    power: u32,
    tau_g1: &[G1Affine],
    tau_g2: &[G2Affine],
    alpha_tau_g1: &[G1Affine],
    beta_tau_g1: &[G1Affine],
    beta_g2: &G2Affine,
) -> Vec<u8> {
    let mut out = Vec::new();
    // Magic, version, num_sections.
    out.extend_from_slice(b"ptau");
    out.extend_from_slice(&1u32.to_le_bytes()); // version
    out.extend_from_slice(&7u32.to_le_bytes()); // 6 data sections + 1 contributions section

    // Section 1: header.
    let modulus_bytes = Fq::MODULUS.to_bytes_le(); // 32 bytes LE
    let mut header_payload = Vec::new();
    header_payload.extend_from_slice(&32u32.to_le_bytes()); // n8
    header_payload.extend_from_slice(&modulus_bytes); // p
    header_payload.extend_from_slice(&power.to_le_bytes());
    header_payload.extend_from_slice(&power.to_le_bytes()); // ceremony_power (mirrors `power`)
    write_section(&mut out, 1, &header_payload);

    // Section 2: tau_g1.
    write_section(&mut out, 2, &serialize_g1_vec(tau_g1));
    // Section 3: tau_g2.
    write_section(&mut out, 3, &serialize_g2_vec(tau_g2));
    // Section 4: alpha_tau_g1.
    write_section(&mut out, 4, &serialize_g1_vec(alpha_tau_g1));
    // Section 5: beta_tau_g1.
    write_section(&mut out, 5, &serialize_g1_vec(beta_tau_g1));
    // Section 6: beta_g2.
    write_section(&mut out, 6, &serialize_g2_vec(&[*beta_g2]));
    // Section 7: contributions (empty).
    write_section(&mut out, 7, &[]);

    out
}

fn write_section(out: &mut Vec<u8>, ty: u32, payload: &[u8]) {
    out.extend_from_slice(&ty.to_le_bytes());
    out.extend_from_slice(&(payload.len() as u64).to_le_bytes());
    out.extend_from_slice(payload);
}

fn serialize_g1_vec(points: &[G1Affine]) -> Vec<u8> {
    let mut out = Vec::with_capacity(points.len() * 64);
    for p in points {
        let (x, y) = if p.is_zero() {
            (Fq::from(0u64), Fq::from(0u64))
        } else {
            p.xy().expect("g1 not zero")
        };
        out.extend_from_slice(&fq_to_mont(x));
        out.extend_from_slice(&fq_to_mont(y));
    }
    out
}

fn serialize_g2_vec(points: &[G2Affine]) -> Vec<u8> {
    let mut out = Vec::with_capacity(points.len() * 128);
    for p in points {
        let (x, y) = if p.is_zero() {
            (ark_bn254::Fq2::ZERO, ark_bn254::Fq2::ZERO)
        } else {
            p.xy().expect("g2 not zero")
        };
        out.extend_from_slice(&fq_to_mont(x.c0));
        out.extend_from_slice(&fq_to_mont(x.c1));
        out.extend_from_slice(&fq_to_mont(y.c0));
        out.extend_from_slice(&fq_to_mont(y.c1));
    }
    out
}

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

// Silence "unused" warnings on conditionally-used items.
#[allow(dead_code)]
fn _silence_field() {
    let _ = Fr::from(0u64);
    let _ = Fq::from(0u64).into_bigint();
}
