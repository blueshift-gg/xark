//! Solana / `alt_bn128`-compatible (Ethereum-compatible) binary encoding for
//! BN254 group elements.
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
//! The big-endian `(c1, c0)` encoders below are the original
//! Ethereum-precompile format; today they are used only as a canonical byte
//! representation for ceremony transcript hashing, which never decodes them.
//! The **on-chain export** (`assemble_{vk,proof,public_inputs}_bytes_le`,
//! consumed by `xark-verifier`) uses the **little-endian** `(c0, c1)` encoders
//! re-exported further down, matching the `alt_bn128_*_le` syscall family.

use ark_bn254::{Fq, G1Affine, G2Affine};
use ark_ec::AffineRepr;
use num_bigint::BigUint;

/// Width in bytes of an encoded Fq field element.
const FIELD_BYTES: usize = 32;

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

// The encoders and the point sizes live in `xark_groth16::solana`, shared with
// xark-wasm so a proof made in a browser becomes the same instruction data.
pub use xark_groth16::solana::{
    FR_BYTES, G1_BYTES, G2_BYTES, assemble_proof_bytes_le, assemble_public_inputs_bytes_le,
    assemble_vk_bytes_le, encode_fr_le, encode_g1_le, encode_g2_le, negate_g1,
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

    /// Each 32-byte coordinate of a little-endian encoding, byte-reversed: the
    /// big-endian bytes of the same coordinates, in the same order.
    fn reverse_coords(le: &[u8]) -> Vec<u8> {
        le.chunks(FIELD_BYTES)
            .flat_map(|c| c.iter().rev().copied())
            .collect()
    }

    #[test]
    fn g1_is_the_le_encoding_byte_reversed() {
        for k in [1u64, 2, 3, 5, 7, 11, 13, 42, 1234, 999_999] {
            let p = g1_for(k);
            let be = encode_g1(&p).to_vec();
            assert_eq!(be, reverse_coords(&encode_g1_le(&p)), "k={k}");
        }
    }

    #[test]
    fn g2_is_the_le_encoding_byte_reversed_with_c1_first() {
        for k in [1u64, 2, 3, 5, 7, 11, 13, 42, 1234, 999_999] {
            let p = g2_for(k);
            // LE wire: x.c0 x.c1 y.c0 y.c1; BE wire: x.c1 x.c0 y.c1 y.c0.
            let reversed = reverse_coords(&encode_g2_le(&p));
            let swapped: Vec<u8> = [1, 0, 3, 2]
                .iter()
                .flat_map(|&i| reversed[i * FIELD_BYTES..][..FIELD_BYTES].to_vec())
                .collect();
            assert_eq!(encode_g2(&p).to_vec(), swapped, "k={k}");
        }
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
    fn point_at_infinity_encodes_to_zeros() {
        assert_eq!(encode_g1(&G1Affine::zero()), [0u8; G1_BYTES]);
        assert_eq!(encode_g2(&G2Affine::zero()), [0u8; G2_BYTES]);
    }
}
