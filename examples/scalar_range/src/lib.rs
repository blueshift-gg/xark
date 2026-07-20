#![no_std]

//! A scalar-field element `s` must be *canonical* (`< n`, not merely
//! limb-bounded `< 2^258`) and nonzero, i.e. `s ∈ [1, n-1]` — this is what makes
//! ECDSA signatures non-malleable. Solving proves knowledge of such an `s`; a
//! non-canonical or zero `s` makes the circuit unsatisfiable.

use xark::{Field, Private};
use xark_secp256k1::affine::Fq;

pub fn circuit(s0: Private<Field>, s1: Private<Field>, s2: Private<Field>) {
    let s = Fq::new([s0, s1, s2]);
    s.assert_canonical(); // 0 <= s < n
    s.assert_nonzero(); // s != 0
}
