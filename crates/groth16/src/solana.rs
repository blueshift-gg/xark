//! The on-chain wire format of `xark-verifier` (Solana's `alt_bn128_*_le`
//! syscalls): every field element 32 bytes little-endian, G2 coordinates as
//! `(c0, c1)`, the point at infinity all zeros. Shared by `xark export` and
//! xark-wasm, so a proof made anywhere becomes the same instruction data.

use ark_bn254::{Bn254, Fq, Fr, G1Affine, G2Affine};
use ark_ec::AffineRepr;
use ark_ff::{BigInteger, PrimeField, Zero};

use crate::{Proof, VerifyingKey};

/// Bytes of an encoded field element (Fq or Fr).
const FIELD_BYTES: usize = 32;
/// Bytes of an encoded G1 point.
pub const G1_BYTES: usize = 64;
/// Bytes of an encoded G2 point.
pub const G2_BYTES: usize = 128;
/// Bytes of an encoded Fr scalar.
pub const FR_BYTES: usize = 32;

fn le<F: PrimeField>(f: &F) -> [u8; FIELD_BYTES] {
    let mut bytes = f.into_bigint().to_bytes_le();
    bytes.resize(FIELD_BYTES, 0);
    bytes.try_into().expect("32 bytes after resize")
}

/// `-p` on G1: `x` kept, `y` replaced by `-y mod q`; infinity is its own inverse.
pub fn negate_g1(p: &G1Affine) -> G1Affine {
    if p.is_zero() {
        return G1Affine::zero();
    }
    let (x, y) = p.xy().expect("g1 not at infinity");
    G1Affine::new_unchecked(x, Fq::zero() - y)
}

/// A G1 point as 64 bytes: `x (32 LE) || y (32 LE)`.
pub fn encode_g1_le(p: &G1Affine) -> [u8; G1_BYTES] {
    let mut out = [0u8; G1_BYTES];
    if let Some((x, y)) = p.xy() {
        out[..32].copy_from_slice(&le(&x));
        out[32..].copy_from_slice(&le(&y));
    }
    out
}

/// A G2 point as 128 bytes: `x.c0 || x.c1 || y.c0 || y.c1`, each 32 B LE.
pub fn encode_g2_le(p: &G2Affine) -> [u8; G2_BYTES] {
    let mut out = [0u8; G2_BYTES];
    if let Some((x, y)) = p.xy() {
        out[0..32].copy_from_slice(&le(&x.c0));
        out[32..64].copy_from_slice(&le(&x.c1));
        out[64..96].copy_from_slice(&le(&y.c0));
        out[96..128].copy_from_slice(&le(&y.c1));
    }
    out
}

/// An Fr scalar as 32 little-endian bytes.
pub fn encode_fr_le(f: &Fr) -> [u8; FR_BYTES] {
    le(f)
}

/// The verifying key as the on-chain verifier embeds it:
/// `α (G1) || β (G2) || γ (G2) || δ (G2) || gamma_abc × G1`. The IC count isn't
/// encoded: it's `(len − 448) / 64`.
pub fn assemble_vk_bytes_le(vk: &VerifyingKey<Bn254>) -> Vec<u8> {
    let mut out = Vec::with_capacity(G1_BYTES + 3 * G2_BYTES + vk.gamma_abc_g1.len() * G1_BYTES);
    out.extend_from_slice(&encode_g1_le(&vk.alpha_g1));
    out.extend_from_slice(&encode_g2_le(&vk.beta_g2));
    out.extend_from_slice(&encode_g2_le(&vk.gamma_g2));
    out.extend_from_slice(&encode_g2_le(&vk.delta_g2));
    for ic in &vk.gamma_abc_g1 {
        out.extend_from_slice(&encode_g1_le(ic));
    }
    out
}

/// A proof as the on-chain verifier takes it (256 bytes): `-A (G1) || B (G2) ||
/// C (G1)`. `A` is pre-negated so the program feeds the pairing directly.
pub fn assemble_proof_bytes_le(proof: &Proof<Bn254>) -> Vec<u8> {
    let mut out = Vec::with_capacity(G1_BYTES + G2_BYTES + G1_BYTES);
    out.extend_from_slice(&encode_g1_le(&negate_g1(&proof.a)));
    out.extend_from_slice(&encode_g2_le(&proof.b));
    out.extend_from_slice(&encode_g1_le(&proof.c));
    out
}

/// Public inputs as the on-chain verifier takes them: 32-byte LE scalars.
pub fn assemble_public_inputs_bytes_le(inputs: &[Fr]) -> Vec<u8> {
    inputs.iter().flat_map(encode_fr_le).collect()
}

/// Bytes of a proof in the on-chain format.
pub const PROOF_BYTES: usize = 2 * G1_BYTES + G2_BYTES;

/// An Fq coordinate from 32 little-endian bytes, refused unless canonical (`< q`).
fn fq_le(b: &[u8]) -> Result<Fq, String> {
    let mut limbs = [0u64; 4];
    for (i, l) in limbs.iter_mut().enumerate() {
        *l = u64::from_le_bytes(b[8 * i..8 * i + 8].try_into().expect("8 bytes"));
    }
    Fq::from_bigint(ark_ff::BigInt(limbs))
        .ok_or_else(|| "a coordinate isn't below the field's modulus".into())
}

fn g1_le(b: &[u8]) -> Result<G1Affine, String> {
    if b.iter().all(|&x| x == 0) {
        return Ok(G1Affine::zero());
    }
    let p = G1Affine::new_unchecked(fq_le(&b[..32])?, fq_le(&b[32..64])?);
    if !p.is_on_curve() || !p.is_in_correct_subgroup_assuming_on_curve() {
        return Err("a G1 point isn't on the curve".into());
    }
    Ok(p)
}

fn g2_le(b: &[u8]) -> Result<G2Affine, String> {
    if b.iter().all(|&x| x == 0) {
        return Ok(G2Affine::zero());
    }
    let x = ark_bn254::Fq2::new(fq_le(&b[0..32])?, fq_le(&b[32..64])?);
    let y = ark_bn254::Fq2::new(fq_le(&b[64..96])?, fq_le(&b[96..128])?);
    let p = G2Affine::new_unchecked(x, y);
    // G2 has a cofactor: a point off the prime-order subgroup would break soundness.
    if !p.is_on_curve() || !p.is_in_correct_subgroup_assuming_on_curve() {
        return Err("a G2 point isn't in the curve's prime-order subgroup".into());
    }
    Ok(p)
}

/// A proof from the on-chain format ([`assemble_proof_bytes_le`]'s 256 bytes), every
/// point checked (canonical coordinates, on the curve, in the right subgroup) and
/// `A` negated back.
pub fn decode_proof_le(bytes: &[u8]) -> Result<Proof<Bn254>, String> {
    if bytes.len() != PROOF_BYTES {
        return Err(format!(
            "an on-chain proof is {PROOF_BYTES} bytes, not {}",
            bytes.len()
        ));
    }
    Ok(Proof {
        a: negate_g1(&g1_le(&bytes[..G1_BYTES])?),
        b: g2_le(&bytes[G1_BYTES..G1_BYTES + G2_BYTES])?,
        c: g1_le(&bytes[G1_BYTES + G2_BYTES..])?,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ec::CurveGroup;

    fn proof() -> Proof<Bn254> {
        Proof {
            a: (G1Affine::generator() * Fr::from(1_234_567u64)).into_affine(),
            b: (G2Affine::generator() * Fr::from(7_654_321u64)).into_affine(),
            c: (G1Affine::generator() * Fr::from(42u64)).into_affine(),
        }
    }

    #[test]
    fn on_chain_proofs_round_trip() {
        let p = proof();
        let bytes = assemble_proof_bytes_le(&p);
        assert_eq!(bytes.len(), PROOF_BYTES);
        let back = decode_proof_le(&bytes).unwrap();
        assert_eq!((back.a, back.b, back.c), (p.a, p.b, p.c));
    }

    #[test]
    fn malformed_on_chain_proofs_are_refused() {
        let bytes = assemble_proof_bytes_le(&proof());
        assert!(decode_proof_le(&bytes[..255]).is_err());
        let mut off_curve = bytes.clone();
        off_curve[0] ^= 1; // A's x: off the curve
        assert!(decode_proof_le(&off_curve).is_err());
        let mut big = bytes.clone();
        big[31] = 0xff; // A's x ≥ q
        assert!(decode_proof_le(&big).is_err());
        let mut b = bytes;
        b[G1_BYTES] ^= 1; // B's x: off the curve (or the subgroup)
        assert!(decode_proof_le(&b).is_err());
    }
}
