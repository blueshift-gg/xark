//! Ed25519 signature-verification example: a succinct ZK proof that a **public**
//! signature verifies — constrain the EdDSA equation `[S]·B == R + [k]·A`. The
//! public key `A`, signature point `R`, scalar `S`, and challenge `k` are all
//! public inputs; the Groth16 proof attests they satisfy the equation, so a
//! verifier checks one short proof instead of the full EC computation.
//!
//! Inputs flatten as aggregates: each `Point` to `<name>.x.limbs[0..2]` /
//! `<name>.y.limbs[0..2]`, and each scalar to `<name>.limbs[0..2]`.
#![no_std]

use xark::Public;
use xark_bignum::scalar_to_bits;
use xark_ed25519::{eddsa_verify, Fq, Point};

pub fn circuit(a: Public<Point>, r: Public<Point>, s: Public<Fq>, k: Public<Fq>) {
    let s_bits = scalar_to_bits(s.limbs);
    let k_bits = scalar_to_bits(k.limbs);
    eddsa_verify(a, r, s_bits, k_bits);
}
