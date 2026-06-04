//! Host-side Arkworks BN254 implementation of the [`Bn128Backend`] trait.
//!
//! This module exists so off-chain tests (in this crate as well as in
//! downstream crates such as `xark-cli`) can exercise
//! [`crate::verifier::verify_groth16_with`] without needing a Solana
//! runtime. Wire format is little-endian to match the deployed program
//! (which uses `alt_bn128_*_le` syscalls).
//!
//! Gated behind the `ark-backend` cargo feature because it pulls in the
//! Arkworks BN254 / EC / FF dependencies that the production on-chain
//! program does not need.

use ark_bn254::{Bn254, Fq, Fq2, Fr, G1Affine, G1Projective, G2Affine};
use ark_ec::{pairing::Pairing, AffineRepr, CurveGroup};
use ark_ff::{One, PrimeField};
use num_bigint::BigUint;

use crate::verifier::{Bn128Backend, VerifierError, FR_BYTES, G1_BYTES, PAIRING_PAIR_BYTES};

const FIELD_BYTES: usize = 32;

fn encode_fq_le(value: &Fq) -> [u8; FIELD_BYTES] {
    let big: BigUint = (*value).into();
    let mut bytes = big.to_bytes_le();
    bytes.resize(FIELD_BYTES, 0);
    bytes.try_into().unwrap()
}

fn decode_fq_le(bytes: &[u8]) -> Fq {
    Fq::from_le_bytes_mod_order(bytes)
}

fn encode_g1_le(p: &G1Affine) -> [u8; G1_BYTES] {
    let mut out = [0u8; G1_BYTES];
    if p.is_zero() {
        return out;
    }
    let (x, y) = p.xy().expect("g1 not at infinity");
    out[..FIELD_BYTES].copy_from_slice(&encode_fq_le(&x));
    out[FIELD_BYTES..].copy_from_slice(&encode_fq_le(&y));
    out
}

fn decode_g1_le(bytes: &[u8]) -> G1Affine {
    if bytes.iter().all(|b| *b == 0) {
        return G1Affine::zero();
    }
    let x = decode_fq_le(&bytes[..FIELD_BYTES]);
    let y = decode_fq_le(&bytes[FIELD_BYTES..]);
    G1Affine::new_unchecked(x, y)
}

fn decode_g2_le(bytes: &[u8]) -> G2Affine {
    if bytes.iter().all(|b| *b == 0) {
        return G2Affine::zero();
    }
    // Solana LE G2 wire format: (x.c0, x.c1, y.c0, y.c1), each 32 B LE.
    let x_c0 = decode_fq_le(&bytes[0..32]);
    let x_c1 = decode_fq_le(&bytes[32..64]);
    let y_c0 = decode_fq_le(&bytes[64..96]);
    let y_c1 = decode_fq_le(&bytes[96..128]);
    let x = Fq2::new(x_c0, x_c1);
    let y = Fq2::new(y_c0, y_c1);
    G2Affine::new_unchecked(x, y)
}

fn decode_fr_le(bytes: &[u8]) -> Fr {
    Fr::from_le_bytes_mod_order(bytes)
}

/// Arkworks-native [`Bn128Backend`] for off-chain testing.
///
/// Drop-in replacement for `SolanaBackend` using the LE wire format. Call
/// sites can swap one for the other with no behavioural difference.
pub struct ArkBackend;

impl Bn128Backend for ArkBackend {
    fn add(input: &[u8]) -> Result<[u8; G1_BYTES], VerifierError> {
        if input.len() != 2 * G1_BYTES {
            return Err(VerifierError::Syscall);
        }
        let a = decode_g1_le(&input[..G1_BYTES]);
        let b = decode_g1_le(&input[G1_BYTES..]);
        let sum = (a + b).into_affine();
        Ok(encode_g1_le(&sum))
    }

    fn mul(input: &[u8]) -> Result<[u8; G1_BYTES], VerifierError> {
        if input.len() != G1_BYTES + FR_BYTES {
            return Err(VerifierError::Syscall);
        }
        let p = decode_g1_le(&input[..G1_BYTES]);
        let s = decode_fr_le(&input[G1_BYTES..]);
        let prod: G1Projective = p * s;
        Ok(encode_g1_le(&prod.into_affine()))
    }

    fn pairing(input: &[u8]) -> Result<bool, VerifierError> {
        if input.is_empty() || input.len() % PAIRING_PAIR_BYTES != 0 {
            return Err(VerifierError::Syscall);
        }
        let n = input.len() / PAIRING_PAIR_BYTES;
        let mut g1s = Vec::with_capacity(n);
        let mut g2s = Vec::with_capacity(n);
        for i in 0..n {
            let off = i * PAIRING_PAIR_BYTES;
            let g1 = decode_g1_le(&input[off..off + G1_BYTES]);
            let g2 = decode_g2_le(&input[off + G1_BYTES..off + PAIRING_PAIR_BYTES]);
            g1s.push(g1);
            g2s.push(g2);
        }
        let pp = Bn254::multi_pairing(g1s, g2s);
        Ok(pp.0.is_one())
    }
}

#[cfg(test)]
mod feature_smoke {
    use super::*;

    #[test]
    fn add_rejects_wrong_length() {
        let err = ArkBackend::add(&[0u8; 17]).expect_err("must reject short input");
        match err {
            VerifierError::Syscall => (),
            other => panic!("expected Syscall, got {other:?}"),
        }
    }
}
