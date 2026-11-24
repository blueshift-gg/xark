//! GLV scalar decomposition for BN254's G1 and G2, in fixed-width arithmetic.
//!
//! Each group has an endomorphism `φ` acting as multiplication by `λ`, so
//! `k·P = k₁·P + k₂·φ(P)` with `k = k₁ + λ·k₂ (mod r)` and `|k₁|, |k₂|` about
//! `√r`: one 254-bit scalar becomes two of [`HALF_BITS`] bits, and an MSM's
//! full-width scalars half as many Pippenger windows over twice the points.
//! The decomposition is arkworks' (`GLVConfig::scalar_decomposition`, the
//! lattice basis `SCALAR_DECOMP_COEFFS`), with its two rounded divisions by `r`
//! done as one multiplication each by a precomputed `2^256·|n|/r`, instead of in
//! allocating big integers, which would cost more than the windows saved.

use std::sync::OnceLock;

use ark_bn254::Fr;
use ark_ec::scalar_mul::glv::GLVConfig;
use ark_ff::{BigInteger, PrimeField};
use num_bigint::BigUint;

use crate::msm::Scalar;

/// A bound on `|k₁|` and `|k₂|`, in bits. The basis vectors are under 2^127 and
/// each rounding is off by at most 1, so each half is under 2^128; the tests
/// check it.
pub const HALF_BITS: usize = 128;

/// One group's decomposition constants.
pub struct Glv {
    /// `round(2^256·|n₂₂|/r)` and `round(2^256·|n₁₂|/r)`, each under 2^130.
    g1: [u64; 3],
    g2: [u64; 3],
    /// `β₁ = s₁·round(k·|n₂₂|/r)`, `β₂ = s₂·round(k·|n₁₂|/r)`: the signs.
    neg_beta1: bool,
    neg_beta2: bool,
    /// The basis, as two's-complement 256-bit integers.
    n: [[u64; 4]; 4],
}

fn limbs(x: &BigUint) -> [u64; 4] {
    let mut out = [0u64; 4];
    for (o, d) in out.iter_mut().zip(x.to_u64_digits()) {
        *o = d;
    }
    out
}

fn neg(x: [u64; 4]) -> [u64; 4] {
    let mut out = [0u64; 4];
    let mut carry = 1u128;
    for i in 0..4 {
        let v = (!x[i]) as u128 + carry;
        out[i] = v as u64;
        carry = v >> 64;
    }
    out
}

fn add(a: [u64; 4], b: [u64; 4]) -> [u64; 4] {
    let mut out = [0u64; 4];
    let mut carry = 0u128;
    for i in 0..4 {
        let v = a[i] as u128 + b[i] as u128 + carry;
        out[i] = v as u64;
        carry = v >> 64;
    }
    out
}

/// `a·b mod 2^256`.
fn mul(a: [u64; 4], b: [u64; 4]) -> [u64; 4] {
    let mut out = [0u64; 4];
    for i in 0..4 {
        let mut carry = 0u128;
        for j in 0..4 - i {
            let v = out[i + j] as u128 + a[i] as u128 * b[j] as u128 + carry;
            out[i + j] = v as u64;
            carry = v >> 64;
        }
    }
    out
}

/// `round(k·g / 2^256)` for `k < 2^256`, `g < 2^192`.
fn mul_shift(k: &[u64; 4], g: &[u64; 3]) -> [u64; 4] {
    let mut p = [0u64; 7];
    for i in 0..4 {
        let mut carry = 0u128;
        for j in 0..3 {
            let v = p[i + j] as u128 + k[i] as u128 * g[j] as u128 + carry;
            p[i + j] = v as u64;
            carry = v >> 64;
        }
        p[i + 3] = carry as u64;
    }
    let mut out = [p[4], p[5], p[6], 0];
    if p[3] >> 63 == 1 {
        out = add(out, [1, 0, 0, 0]);
    }
    out
}

impl Glv {
    fn new<C: GLVConfig<ScalarField = Fr>>() -> Self {
        let r: BigUint = Fr::MODULUS.into();
        let two256 = BigUint::from(1u8) << 256;
        let c = C::SCALAR_DECOMP_COEFFS;
        let mag = |i: usize| -> BigUint { c[i].1.into() };
        let signed = |i: usize| {
            let m = limbs(&mag(i));
            if c[i].0 { m } else { neg(m) }
        };
        let g = |m: BigUint| {
            let q = (&two256 * m + (&r >> 1u32)) / &r;
            let l = limbs(&q);
            assert_eq!(l[3], 0, "GLV constant too wide");
            [l[0], l[1], l[2]]
        };
        Glv {
            g1: g(mag(3)),
            g2: g(mag(1)),
            // β₁ = round(k·n₂₂/r) and β₂ = round(−k·n₁₂/r).
            neg_beta1: !c[3].0,
            neg_beta2: c[1].0,
            n: [signed(0), signed(1), signed(2), signed(3)],
        }
    }

    /// `k = k₁ + λ·k₂ (mod r)` for `k < r`: `((k₁ ≥ 0, |k₁|), (k₂ ≥ 0, |k₂|))`.
    #[inline]
    pub fn decompose(&self, k: &Scalar) -> ((bool, Scalar), (bool, Scalar)) {
        let k = k.0;
        let signed = |neg_it: bool, x: [u64; 4]| if neg_it { neg(x) } else { x };
        let b1 = signed(self.neg_beta1, mul_shift(&k, &self.g1));
        let b2 = signed(self.neg_beta2, mul_shift(&k, &self.g2));
        let [n11, n12, n21, n22] = self.n;
        // k₁ = k − (β₁·n₁₁ + β₂·n₂₁), k₂ = −(β₁·n₁₂ + β₂·n₂₂): exact in 256-bit
        // two's complement, since each is small.
        let k1 = add(k, neg(add(mul(b1, n11), mul(b2, n21))));
        let k2 = neg(add(mul(b1, n12), mul(b2, n22)));
        let split = |x: [u64; 4]| {
            if x[3] >> 63 == 1 {
                (false, ark_ff::BigInt(neg(x)))
            } else {
                (true, ark_ff::BigInt(x))
            }
        };
        (split(k1), split(k2))
    }
}

/// G1's decomposition.
pub fn g1() -> &'static Glv {
    static G: OnceLock<Glv> = OnceLock::new();
    G.get_or_init(Glv::new::<ark_bn254::g1::Config>)
}

/// G2's decomposition.
pub fn g2() -> &'static Glv {
    static G: OnceLock<Glv> = OnceLock::new();
    G.get_or_init(Glv::new::<ark_bn254::g2::Config>)
}

/// `true` if `k`'s magnitude fits [`HALF_BITS`].
pub fn fits(k: &Scalar) -> bool {
    k.num_bits() as usize <= HALF_BITS
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ff::{Field, UniformRand, Zero};
    use rand::SeedableRng;

    fn check<C: GLVConfig<ScalarField = Fr>>(glv: &Glv, k: Fr) {
        let ((s1, k1), (s2, k2)) = glv.decompose(&k.into_bigint());
        assert!(fits(&k1) && fits(&k2), "{k}: {k1} {k2}");
        let f = |s: bool, x: Scalar| {
            let v = Fr::from_bigint(x).unwrap();
            if s { v } else { -v }
        };
        assert_eq!(f(s1, k1) + C::LAMBDA * f(s2, k2), k);
    }

    #[test]
    fn decomposition_recombines_with_short_halves() {
        let mut rng = rand_chacha::ChaCha20Rng::seed_from_u64(5);
        let edges = [
            Fr::zero(),
            Fr::from(1u64),
            -Fr::from(1u64),
            Fr::from(2u64).pow([253u64]),
            <ark_bn254::g1::Config as GLVConfig>::LAMBDA,
        ];
        for k in edges
            .into_iter()
            .chain((0..20_000).map(|_| Fr::rand(&mut rng)))
        {
            check::<ark_bn254::g1::Config>(g1(), k);
            check::<ark_bn254::g2::Config>(g2(), k);
        }
    }
}
