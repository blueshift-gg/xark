//! Full secp256r1 (P-256) ECDSA verification, 3-limb (86-bit) path.
//!
//! Inputs are passed **directly as aggregates**: the public key `q: Point`
//! flattens to `q.x.limbs[0..2]`/`q.y.limbs[0..2]`, and each scalar `Fq` to
//! `r.limbs[0..2]`/`s.limbs[0..2]`/`e.limbs[0..2]`.
#![no_std]
use xark::Public;
use xark_secp256r1::{ecdsa_verify, Fq, Point};

pub fn circuit(q: Public<Point>, r: Public<Fq>, s: Public<Fq>, e: Public<Fq>) {
    ecdsa_verify(q, r, s, e);
}
