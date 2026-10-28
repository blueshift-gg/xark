//! Compressed point decoding — the same points as arkworks'
//! `deserialize_with_mode(Compress::Yes, Validate::No)`, with cheaper square roots.
//!
//! Decompressing the proving key is most of a proof's work with a compressed key:
//! one square root in `Fq` per G1 point, one in `Fq2` per G2 point. Two savings:
//!
//! * Exponentiations use a 4-bit fixed window (~13% fewer multiplications than
//!   plain square-and-multiply).
//! * The `Fq2` root (complex method) needs `√α` for the norm α, then `√δ` and
//!   `1/√δ` for `δ = (α' + c0)/2`. Arkworks computes a Legendre symbol, a square
//!   root and an inversion for the second part; one exponentiation
//!   `t = δ^((p−3)/4)` gives all three: `√δ = t·δ`, and `t·√δ = δ^((p−1)/2)` is
//!   the Legendre symbol, which when it is 1 makes `t = 1/√δ`.
//!
//! The roots are the same field elements arkworks computes, so the decoded points
//! are bit-identical (tested against arkworks, both signs, infinity, invalid
//! encodings).

use ark_bn254::{Fq, Fq2, G1Affine, G2Affine};
use ark_ec::AffineRepr;
use ark_ff::{BigInt, BigInteger, Field, One, PrimeField, Zero};
use ark_serialize::{CanonicalDeserialize, Compress, SerializationError, Validate};
use std::sync::OnceLock;

/// `a^e` with a 4-bit fixed window (`e` little-endian limbs).
fn pow_window(a: Fq, e: &BigInt<4>) -> Fq {
    let mut table = [Fq::one(); 16];
    for i in 1..16 {
        table[i] = table[i - 1] * a;
    }
    let mut acc = Fq::one();
    let mut started = false;
    for limb in e.0.iter().rev() {
        for nib in (0..16).rev() {
            let d = ((limb >> (4 * nib)) & 0xf) as usize;
            if started {
                for _ in 0..4 {
                    acc.square_in_place();
                }
                if d != 0 {
                    acc *= table[d];
                }
            } else if d != 0 {
                acc = table[d];
                started = true;
            }
        }
    }
    acc
}

struct Exps {
    /// `(p+1)/4`: `√a = a^((p+1)/4)` for a square `a` (`p ≡ 3 mod 4`).
    sqrt: BigInt<4>,
    /// `(p−3)/4`.
    inv_sqrt: BigInt<4>,
    two_inv: Fq,
}

fn exps() -> &'static Exps {
    static E: OnceLock<Exps> = OnceLock::new();
    E.get_or_init(|| {
        let mut sqrt = Fq::MODULUS;
        sqrt.add_with_carry(&BigInt::from(1u64));
        sqrt.div2();
        sqrt.div2();
        let mut inv_sqrt = sqrt;
        inv_sqrt.sub_with_borrow(&BigInt::from(1u64));
        Exps {
            sqrt,
            inv_sqrt,
            two_inv: Fq::from(2u64).inverse().unwrap(),
        }
    })
}

/// arkworks' `Fq::sqrt` (same root), with the windowed exponentiation.
fn sqrt_fq(a: Fq) -> Option<Fq> {
    let r = pow_window(a, &exps().sqrt);
    (r.square() == a).then_some(r)
}

/// arkworks' `Fq2::sqrt` (complex method, same root), with one exponentiation for
/// `√δ`, `1/√δ` and the residuosity test.
fn sqrt_fq2(a: Fq2) -> Option<Fq2> {
    if a.c1.is_zero() {
        return a.sqrt(); // rare: defer to arkworks' branch for real inputs
    }
    let e = exps();
    // BN254's Fq2 = Fq[u]/(u² + 1): the norm is c0² + c1².
    let alpha = a.c0.square() + a.c1.square();
    let s = sqrt_fq(alpha)?;
    let delta = (s + a.c0) * e.two_inv;
    let root_and_inv = |d: Fq| -> Option<(Fq, Fq)> {
        let t = pow_window(d, &e.inv_sqrt);
        let r = t * d;
        (r * t == Fq::one()).then_some((r, t))
    };
    // arkworks: if δ is a non-residue, use δ − √α instead.
    let (c0, c0_inv) = match root_and_inv(delta) {
        Some(x) => x,
        None => root_and_inv(delta - s)?,
    };
    let cand = Fq2::new(c0, a.c1 * e.two_inv * c0_inv);
    (cand.square() == a).then_some(cand)
}

/// `x` from `n` little-endian bytes whose last byte carries the two flag bits.
fn fq_from_le(b: &[u8]) -> Result<Fq, SerializationError> {
    let mut limbs = [0u64; 4];
    for (i, chunk) in b.chunks(8).enumerate() {
        limbs[i] = u64::from_le_bytes(chunk.try_into().unwrap());
    }
    Fq::from_bigint(BigInt::new(limbs)).ok_or(SerializationError::InvalidData)
}

/// `(infinity, larger_y)` from a flag byte, rejecting both bits set.
fn flags(last: u8) -> Result<(bool, bool), SerializationError> {
    match (last >> 7 & 1 == 1, last >> 6 & 1 == 1) {
        (true, true) => Err(SerializationError::UnexpectedFlags),
        (neg, inf) => Ok((inf, neg)),
    }
}

/// Strip the flag bits off a copy of the final byte.
fn unflagged<const N: usize>(b: &[u8]) -> [u8; N] {
    let mut out: [u8; N] = b.try_into().unwrap();
    out[N - 1] &= 0x3f;
    out
}

/// One compressed G1 point (32 bytes).
pub fn g1(b: &[u8]) -> Result<G1Affine, SerializationError> {
    if b.len() != 32 {
        return Err(SerializationError::InvalidData);
    }
    let (inf, larger) = flags(b[31])?;
    let x = fq_from_le(&unflagged::<32>(b))?;
    if inf {
        return Ok(G1Affine::zero());
    }
    // y² = x³ + 3.
    let y = sqrt_fq(x.square() * x + Fq::from(3u64)).ok_or(SerializationError::InvalidData)?;
    let neg = -y;
    let (small, large) = if y < neg { (y, neg) } else { (neg, y) };
    Ok(G1Affine::new_unchecked(
        x,
        if larger { large } else { small },
    ))
}

/// One compressed G2 point (64 bytes: `x.c0 ‖ x.c1`, flags on the last byte).
pub fn g2(b: &[u8]) -> Result<G2Affine, SerializationError> {
    if b.len() != 64 {
        return Err(SerializationError::InvalidData);
    }
    let (inf, larger) = flags(b[63])?;
    let x = Fq2::new(
        fq_from_le(&b[..32])?,
        fq_from_le(&unflagged::<32>(&b[32..]))?,
    );
    if inf {
        return Ok(G2Affine::zero());
    }
    let rhs = x.square() * x
        + <ark_bn254::g2::Config as ark_ec::short_weierstrass::SWCurveConfig>::COEFF_B;
    let y = sqrt_fq2(rhs).ok_or(SerializationError::InvalidData)?;
    let neg = -y;
    let (small, large) = if y < neg { (y, neg) } else { (neg, y) };
    Ok(G2Affine::new_unchecked(
        x,
        if larger { large } else { small },
    ))
}

/// A point type with a fast compressed decoder.
pub trait Decode: CanonicalDeserialize {
    fn decode_compressed(b: &[u8]) -> Result<Self, SerializationError>;
}

impl Decode for ark_ec::short_weierstrass::Affine<ark_bn254::g1::Config> {
    fn decode_compressed(b: &[u8]) -> Result<Self, SerializationError> {
        g1(b)
    }
}

impl Decode for ark_ec::short_weierstrass::Affine<ark_bn254::g2::Config> {
    fn decode_compressed(b: &[u8]) -> Result<Self, SerializationError> {
        g2(b)
    }
}

/// One serialized point, unchecked like `deserialize_with_mode(_, Validate::No)`.
pub fn point<A: Decode>(b: &[u8], c: Compress) -> Result<A, SerializationError> {
    match c {
        Compress::Yes => A::decode_compressed(b),
        Compress::No => A::deserialize_with_mode(b, Compress::No, Validate::No),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ec::CurveGroup;
    use ark_ff::UniformRand;
    use ark_serialize::CanonicalSerialize;
    use rand::SeedableRng;

    fn ark<A: CanonicalDeserialize>(b: &[u8]) -> Result<A, SerializationError> {
        A::deserialize_with_mode(b, Compress::Yes, Validate::No)
    }

    #[test]
    fn matches_arkworks_on_random_points_and_edge_cases() {
        let mut rng = rand_chacha::ChaCha20Rng::seed_from_u64(9);
        for i in 0..3000 {
            let p = ark_bn254::G1Projective::rand(&mut rng).into_affine();
            let q = ark_bn254::G2Projective::rand(&mut rng).into_affine();
            for (p, q) in [(p, q), (-p, -q)] {
                let (mut bp, mut bq) = (Vec::new(), Vec::new());
                p.serialize_compressed(&mut bp).unwrap();
                q.serialize_compressed(&mut bq).unwrap();
                assert_eq!(g1(&bp).unwrap(), p, "g1 #{i}");
                assert_eq!(g2(&bq).unwrap(), q, "g2 #{i}");
            }
            // Random bytes: same verdict and (when valid) same point as arkworks.
            let mut junk = [0u8; 64];
            for (j, b) in junk.iter_mut().enumerate() {
                *b = (i as u8)
                    .wrapping_mul(31)
                    .wrapping_add((j as u8).wrapping_mul(7))
                    ^ 0x5a;
            }
            junk[31] &= 0x3f;
            junk[63] &= 0x3f;
            assert_eq!(
                g1(&junk[..32]).ok(),
                ark::<G1Affine>(&junk[..32]).ok(),
                "g1 junk #{i}"
            );
            assert_eq!(g2(&junk).ok(), ark::<G2Affine>(&junk).ok(), "g2 junk #{i}");
        }
        for (a, b) in [
            (G1Affine::zero(), G2Affine::zero()),
            (G1Affine::generator(), G2Affine::generator()),
        ] {
            let (mut bp, mut bq) = (Vec::new(), Vec::new());
            a.serialize_compressed(&mut bp).unwrap();
            b.serialize_compressed(&mut bq).unwrap();
            assert_eq!(g1(&bp).unwrap(), a);
            assert_eq!(g2(&bq).unwrap(), b);
        }
        // Both flag bits set, and x ≥ p, are rejected like arkworks does.
        let mut bad = [0u8; 32];
        bad[31] = 0xc0;
        assert!(g1(&bad).is_err() && ark::<G1Affine>(&bad).is_err());
        let over = [0xffu8; 32];
        let mut over_ok = over;
        over_ok[31] = 0x3f;
        assert!(g1(&over_ok).is_err() && ark::<G1Affine>(&over_ok).is_err());
    }
}
