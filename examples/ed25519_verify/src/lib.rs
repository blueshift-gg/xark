//! Ed25519 signature-verification example: constrain the EdDSA equation
//! `[S]·B == R + [k]·A`. The public key `A` and signature point `R` are given as
//! aggregate `Point`s; the signature scalar `S` and challenge `k` are given as
//! three 86-bit limbs each (decomposed to bits in-circuit).
//!
//! Inputs are passed **directly as aggregates**: each `Point` flattens to
//! `<name>.x.limbs[0..2]`/`<name>.y.limbs[0..2]`, and each scalar to `s[0..2]`/
//! `k[0..2]`.
#![no_std]

use xark_ed25519::{eddsa_verify, Point};
use xark_ff::scalar_to_bits;
use xark::{Field, Private, Public};

pub fn circuit(
    a: Public<Point>,
    r: Public<Point>,
    s: Private<[Field; 3]>,
    k: Private<[Field; 3]>,
) {
    let s_bits = scalar_to_bits(s);
    let k_bits = scalar_to_bits(k);
    eddsa_verify(a, r, s_bits, k_bits);
}
