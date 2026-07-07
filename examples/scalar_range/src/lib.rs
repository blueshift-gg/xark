#![no_std]

//! Exercises the ECDSA scalar-range checks (audit #08): a scalar-field element
//! `s` must be *canonical* (`< n`, not merely limb-bounded `< 2^258`) and
//! nonzero, i.e. `s ∈ [1, n-1]`. This is what closes ECDSA signature
//! malleability. Solving proves knowledge of such an `s`; a non-canonical or
//! zero `s` makes the circuit unsatisfiable.

use xark::{Field, Private};
use xark_secp256k1::Fq;

pub fn circuit(s0: Private<Field>, s1: Private<Field>, s2: Private<Field>) {
    let s = Fq::new([s0, s1, s2]);
    s.assert_canonical(); // 0 <= s < n
    s.assert_nonzero(); // s != 0
}
