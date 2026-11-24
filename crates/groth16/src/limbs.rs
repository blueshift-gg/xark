//! Field addition and subtraction on Montgomery limbs, for the hot loops.
//!
//! arkworks' `+` and `−` on a 4-limb field compare the result against the
//! modulus limb by limb; these share the loads, reduce with one branch-free
//! select, and leave the result canonical, so they give the same elements.
//! Measured on Apple M3: `Fq` subtraction 2.7 ns in arkworks; the FFT butterfly
//! went from 17.6 to 12.0 ns with them.

use ark_ff::{BigInt, Fp, FpConfig, PrimeField};

/// `a + b mod p`, for canonical `a, b < p < 2^255`.
#[inline(always)]
pub fn add(a: &[u64; 4], b: &[u64; 4], p: &[u64; 4]) -> [u64; 4] {
    let mut sum = [0u64; 4];
    let mut carry = 0u64;
    for i in 0..4 {
        let (x, c1) = a[i].overflowing_add(b[i]);
        let (x, c2) = x.overflowing_add(carry);
        sum[i] = x;
        carry = (c1 | c2) as u64;
    }
    let mut red = [0u64; 4];
    let mut borrow = 0u64;
    for i in 0..4 {
        let (x, b1) = sum[i].overflowing_sub(p[i]);
        let (x, b2) = x.overflowing_sub(borrow);
        red[i] = x;
        borrow = (b1 | b2) as u64;
    }
    // sum < p exactly when sum − p borrows.
    let keep = 0u64.wrapping_sub(borrow);
    let mut out = [0u64; 4];
    for i in 0..4 {
        out[i] = (sum[i] & keep) | (red[i] & !keep);
    }
    out
}

/// `a − b mod p`, for canonical `a, b < p`.
#[inline(always)]
pub fn sub(a: &[u64; 4], b: &[u64; 4], p: &[u64; 4]) -> [u64; 4] {
    let mut diff = [0u64; 4];
    let mut borrow = 0u64;
    for i in 0..4 {
        let (x, b1) = a[i].overflowing_sub(b[i]);
        let (x, b2) = x.overflowing_sub(borrow);
        diff[i] = x;
        borrow = (b1 | b2) as u64;
    }
    // a − b < 0: add p back.
    let add = 0u64.wrapping_sub(borrow);
    let mut carry = 0u64;
    for i in 0..4 {
        let (x, c1) = diff[i].overflowing_add(p[i] & add);
        let (x, c2) = x.overflowing_add(carry);
        diff[i] = x;
        carry = (c1 | c2) as u64;
    }
    diff
}

/// Fast subtraction for an MSM's base field.
pub trait FastSub: Sized {
    fn fsub(&self, b: &Self) -> Self;
}

impl<P: FpConfig<4>> FastSub for Fp<P, 4> {
    #[inline(always)]
    fn fsub(&self, b: &Self) -> Self {
        let m = <Self as PrimeField>::MODULUS.0;
        Fp(
            BigInt(sub(&self.0.0, &b.0.0, &m)),
            core::marker::PhantomData,
        )
    }
}

impl FastSub for ark_bn254::Fq2 {
    #[inline(always)]
    fn fsub(&self, b: &Self) -> Self {
        ark_bn254::Fq2::new(self.c0.fsub(&b.c0), self.c1.fsub(&b.c1))
    }
}
