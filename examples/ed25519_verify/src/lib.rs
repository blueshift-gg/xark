//! Ed25519 signature-verification example: a succinct ZK proof that a **public**
//! signature verifies — constrain the EdDSA equation `[S]·B == R + [k]·A`. The
//! public key `A`, signature point `R`, scalar `S`, and challenge `k` are all
//! public inputs; the Groth16 proof attests they satisfy the equation.
//!
//! Uses the **sound lazy extended-coordinate** path (`eddsa_verify_lazy`): point
//! coordinates are 3×85-bit limbs (`PointL`), scalars are 3×86-bit `Fq`. It
//! verifies in ~2.36M constraints (vs the affine gadget's 4.55M) while staying
//! sound. Inputs flatten as aggregates: each `PointL` to `<name>.x.limbs[0..2]` /
//! `<name>.y.limbs[0..2]`, and each scalar to `<name>.limbs[0..2]`.
#![no_std]

use xark::Public;
use xark_bignum::scalar_to_bits;
use xark_ed25519::{eddsa_verify_lazy, Fq, PointL};

pub fn circuit(a: Public<PointL>, r: Public<PointL>, s: Public<Fq>, k: Public<Fq>) {
    eddsa_verify_lazy(
        a.x.limbs,
        a.y.limbs,
        r.x.limbs,
        r.y.limbs,
        scalar_to_bits(s.limbs),
        scalar_to_bits(k.limbs),
    );
}
