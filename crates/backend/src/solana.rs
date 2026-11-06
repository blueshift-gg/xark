//! Solana / `alt_bn128`-compatible (Ethereum-compatible) binary encoding for
//! BN254 group elements and scalars.
//!
//! Solana exposes the BN254 pairing-friendly group operations through three
//! syscalls (`sol_alt_bn128_addition`, `sol_alt_bn128_multiplication`,
//! `sol_alt_bn128_pairing`). All three consume and emit points in the exact
//! same wire format as the Ethereum precompiles (`0x06`, `0x07`, `0x08`):
//!
//! * **G1Affine** is encoded as 64 bytes: `x (32 BE) || y (32 BE)`, each Fq
//!   coordinate big-endian.
//! * **G2Affine** is encoded as 128 bytes: `x.c1 || x.c0 || y.c1 || y.c0`,
//!   each component a 32-byte big-endian Fq value. Note the **`(c1, c0)`
//!   order** — imaginary part first, real part second.
//! * **Fr** scalars are 32 bytes big-endian.
//! * The **point at infinity** is the all-zeros buffer (64 bytes for G1,
//!   128 bytes for G2).
//!
//! ## Why `(c1, c0)` instead of `(c0, c1)`?
//!
//! Arkworks stores `Fq2 { c0, c1 }` internally (real, imaginary). The
//! Ethereum BN254 precompiles flip the order on the wire, exposing `(c1, c0)`.
//! This module hides that quirk; callers always speak in arkworks-native types.
//!
//! ## Big-endian vs little-endian
//!
//! The big-endian `(c1, c0)` encoders above are the original
//! Ethereum-precompile format; today they are used only as a canonical byte
//! representation for ceremony transcript hashing. The **on-chain export**
//! (`assemble_{vk,proof,public_inputs}_bytes_le`, consumed by `xark-verifier`)
//! uses the **little-endian** `(c0, c1)` encoders further down, matching the
//! `alt_bn128_*_le` syscall family. See those sections below.

use ark_bn254::{Fq, Fq2, Fr, G1Affine, G2Affine};
use ark_ec::AffineRepr;
use ark_ff::PrimeField;
use num_bigint::BigUint;

/// Width in bytes of an encoded Fq / Fr field element.
const FIELD_BYTES: usize = 32;
/// Width in bytes of an encoded G1 point.
pub const G1_BYTES: usize = 64;
/// Width in bytes of an encoded G2 point.
pub const G2_BYTES: usize = 128;
/// Width in bytes of an encoded Fr scalar.
pub const FR_BYTES: usize = 32;

/// Encode an Fq element as 32 big-endian bytes (zero-padded on the left).
fn encode_fq(value: &Fq) -> [u8; FIELD_BYTES] {
    let big: BigUint = (*value).into();
    let bytes = big.to_bytes_be();
    let mut out = [0u8; FIELD_BYTES];
    // `bytes.len()` may be shorter than 32 if `value` has leading zeros.
    let offset = FIELD_BYTES - bytes.len();
    out[offset..].copy_from_slice(&bytes);
    out
}

/// Decode 32 big-endian bytes into an Fq element (reduced modulo `p`).
fn decode_fq(bytes: &[u8]) -> Fq {
    Fq::from_be_bytes_mod_order(bytes)
}

/// Encode a G1 affine point as 64 bytes: `x (32 BE) || y (32 BE)`.
/// The point at infinity becomes 64 zero bytes.
pub fn encode_g1(p: &G1Affine) -> [u8; G1_BYTES] {
    let mut out = [0u8; G1_BYTES];
    if p.is_zero() {
        return out;
    }
    let (x, y) = p.xy().expect("g1 not at infinity");
    out[..FIELD_BYTES].copy_from_slice(&encode_fq(&x));
    out[FIELD_BYTES..].copy_from_slice(&encode_fq(&y));
    out
}

/// Decode 64 bytes into a G1 affine point. An all-zero buffer decodes to
/// the point at infinity. No subgroup check is performed (matches the
/// behavior of the on-chain syscalls, which check internally).
pub fn decode_g1(bytes: &[u8; G1_BYTES]) -> G1Affine {
    if bytes.iter().all(|b| *b == 0) {
        return G1Affine::zero();
    }
    let x = decode_fq(&bytes[..FIELD_BYTES]);
    let y = decode_fq(&bytes[FIELD_BYTES..]);
    G1Affine::new_unchecked(x, y)
}

/// Encode a G2 affine point as 128 bytes:
/// `x.c1 || x.c0 || y.c1 || y.c0`. The point at infinity becomes 128
/// zero bytes. **Imaginary part comes first** — see module docs.
pub fn encode_g2(p: &G2Affine) -> [u8; G2_BYTES] {
    let mut out = [0u8; G2_BYTES];
    if p.is_zero() {
        return out;
    }
    let (x, y) = p.xy().expect("g2 not at infinity");
    // Arkworks Fq2 = { c0, c1 }. Wire format is (c1, c0).
    out[0..32].copy_from_slice(&encode_fq(&x.c1));
    out[32..64].copy_from_slice(&encode_fq(&x.c0));
    out[64..96].copy_from_slice(&encode_fq(&y.c1));
    out[96..128].copy_from_slice(&encode_fq(&y.c0));
    out
}

/// Decode 128 bytes into a G2 affine point. Handles the `(c1, c0)` wire
/// order. An all-zero buffer decodes to the point at infinity.
pub fn decode_g2(bytes: &[u8; G2_BYTES]) -> G2Affine {
    if bytes.iter().all(|b| *b == 0) {
        return G2Affine::zero();
    }
    let x_c1 = decode_fq(&bytes[0..32]);
    let x_c0 = decode_fq(&bytes[32..64]);
    let y_c1 = decode_fq(&bytes[64..96]);
    let y_c0 = decode_fq(&bytes[96..128]);
    let x = Fq2::new(x_c0, x_c1);
    let y = Fq2::new(y_c0, y_c1);
    G2Affine::new_unchecked(x, y)
}

/// Encode an Fr scalar as 32 big-endian bytes (zero-padded on the left).
pub fn encode_fr(f: &Fr) -> [u8; FR_BYTES] {
    let big: BigUint = (*f).into();
    let bytes = big.to_bytes_be();
    let mut out = [0u8; FR_BYTES];
    let offset = FR_BYTES - bytes.len();
    out[offset..].copy_from_slice(&bytes);
    out
}

/// Decode 32 big-endian bytes into an Fr scalar (reduced modulo `r`).
pub fn decode_fr(bytes: &[u8; FR_BYTES]) -> Fr {
    Fr::from_be_bytes_mod_order(bytes)
}

// =============================================================================
// Little-endian variants for the `alt_bn128_*_le` syscall family.
// =============================================================================
//
// `solana-bn254 3.x` exposed explicit LE syscalls (`alt_bn128_g1_addition_le`,
// `_g1_multiplication_le`, `_pairing_le`) that consume / emit each Fq and Fr
// in 32-byte little-endian. The xark-verifier crate uses those by
// default because LE matches Solana's native byte order for borsh /
// borsh-derive and matches Anza's documented forward direction for these
// precompiles.
//
// The point-at-infinity sentinel is unchanged (all-zero buffer).
// G2's Fq2 component order is `(c0, c1)` on the LE wire (the historic
// `(c1, c0)` flip was a quirk of the Ethereum-compat BE format that the LE
// variants don't preserve).

// The encoders themselves live in `xark_groth16::solana`, shared with xark-wasm
// so a proof made in a browser becomes the same instruction data.
pub use xark_groth16::solana::{
    assemble_proof_bytes_le, assemble_public_inputs_bytes_le, assemble_vk_bytes_le, encode_fr_le,
    encode_g1_le, encode_g2_le, negate_g1,
};

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bn254::{Fq, Fq2, Fr, G1Affine, G2Affine};
    use ark_ec::{AffineRepr, CurveGroup};
    use ark_ff::Zero;

    fn g1_for(k: u64) -> G1Affine {
        (G1Affine::generator() * Fr::from(k)).into_affine()
    }

    fn g2_for(k: u64) -> G2Affine {
        (G2Affine::generator() * Fr::from(k)).into_affine()
    }

    #[test]
    fn roundtrip_g1_random() {
        for k in [1u64, 2, 3, 5, 7, 11, 13, 42, 1234, 999_999] {
            let p = g1_for(k);
            let bytes = encode_g1(&p);
            let back = decode_g1(&bytes);
            assert_eq!(p, back, "G1 roundtrip failed for k={k}");
        }
    }

    #[test]
    fn roundtrip_g2_random() {
        for k in [1u64, 2, 3, 5, 7, 11, 13, 42, 1234, 999_999] {
            let p = g2_for(k);
            let bytes = encode_g2(&p);
            let back = decode_g2(&bytes);
            assert_eq!(p, back, "G2 roundtrip failed for k={k}");
        }
    }

    #[test]
    fn roundtrip_fr() {
        for k in [0u64, 1, 2, 3, 7, 42, 1_000_000_007, u64::MAX] {
            let f = Fr::from(k);
            let bytes = encode_fr(&f);
            let back = decode_fr(&bytes);
            assert_eq!(f, back, "Fr roundtrip failed for k={k}");
        }
        // Cover a non-u64-derived value too: -1 (i.e. r-1).
        let neg_one = Fr::from(0u64) - Fr::from(1u64);
        let bytes = encode_fr(&neg_one);
        let back = decode_fr(&bytes);
        assert_eq!(neg_one, back, "Fr roundtrip failed for -1");
    }

    #[test]
    fn g2_c1_c0_ordering_documented() {
        // Build a deterministic non-trivial G2 point and confirm that bytes
        // 0..32 hold x.c1 (imaginary) and bytes 32..64 hold x.c0 (real).
        let p = g2_for(7);
        let (x, y) = p.xy().expect("g2 not at infinity");
        let Fq2 { c0: x_c0, c1: x_c1 } = x;
        let Fq2 { c0: y_c0, c1: y_c1 } = y;

        // Sanity: pick a point whose c0 != c1 on both coordinates so the
        // ordering check is meaningful.
        assert_ne!(x_c0, x_c1, "test point has degenerate x.c0 == x.c1");
        assert_ne!(y_c0, y_c1, "test point has degenerate y.c0 == y.c1");

        let bytes = encode_g2(&p);
        assert_eq!(
            &bytes[0..32],
            &encode_fq(&x_c1),
            "byte slot 0..32 must be x.c1"
        );
        assert_eq!(
            &bytes[32..64],
            &encode_fq(&x_c0),
            "byte slot 32..64 must be x.c0"
        );
        assert_eq!(
            &bytes[64..96],
            &encode_fq(&y_c1),
            "byte slot 64..96 must be y.c1"
        );
        assert_eq!(
            &bytes[96..128],
            &encode_fq(&y_c0),
            "byte slot 96..128 must be y.c0"
        );

        // And decoding flips them back correctly.
        let back = decode_g2(&bytes);
        assert_eq!(back, p);
    }

    #[test]
    fn negate_g1_inverts_pairing_addition() {
        for k in [1u64, 2, 3, 7, 99, 12345] {
            let p = g1_for(k);
            let neg = negate_g1(&p);
            assert_ne!(neg, p, "negate_g1 must change a non-identity point");
            let sum = (p + neg).into_affine();
            assert!(sum.is_zero(), "p + (-p) must be the identity for k={k}");
        }
    }

    #[test]
    fn negate_g1_preserves_x() {
        // Spot-check that negation keeps x and flips y.
        let p = g1_for(13);
        let neg = negate_g1(&p);
        let (px, py) = p.xy().unwrap();
        let (nx, ny) = neg.xy().unwrap();
        assert_eq!(px, nx, "x must be preserved under G1 negation");
        assert_eq!(ny, Fq::zero() - py, "y must be flipped under G1 negation");
    }

    #[test]
    fn negate_g1_handles_infinity() {
        let zero = G1Affine::zero();
        let neg = negate_g1(&zero);
        assert!(neg.is_zero(), "negate(O) must remain O");
    }

    #[test]
    fn point_at_infinity_round_trips() {
        // G1 identity.
        let g1_zero = G1Affine::zero();
        let g1_bytes = encode_g1(&g1_zero);
        assert_eq!(
            g1_bytes, [0u8; G1_BYTES],
            "G1 infinity must encode to zeros"
        );
        let g1_back = decode_g1(&g1_bytes);
        assert_eq!(g1_back, g1_zero);

        // G2 identity.
        let g2_zero = G2Affine::zero();
        let g2_bytes = encode_g2(&g2_zero);
        assert_eq!(
            g2_bytes, [0u8; G2_BYTES],
            "G2 infinity must encode to zeros"
        );
        let g2_back = decode_g2(&g2_bytes);
        assert_eq!(g2_back, g2_zero);
    }
}
