#![no_std]

use xark::{Field, Private};
use xark_secp256k1::{ecdsa_verify, Fp, Fq, Point};

// ecdsa_basic: verify a secp256k1 ECDSA signature; all inputs are
// private (0 public inputs). The public
// key `q`, signature `(r, s)`, and message scalar `e` are supplied as 3-limb
// (86-bit) field-element encodings; the gadget asserts `R.x mod n == r`.
#[allow(clippy::too_many_arguments)]
pub fn circuit(
    qx0: Private<Field>,
    qx1: Private<Field>,
    qx2: Private<Field>,
    qy0: Private<Field>,
    qy1: Private<Field>,
    qy2: Private<Field>,
    r0: Private<Field>,
    r1: Private<Field>,
    r2: Private<Field>,
    s0: Private<Field>,
    s1: Private<Field>,
    s2: Private<Field>,
    e0: Private<Field>,
    e1: Private<Field>,
    e2: Private<Field>,
) {
    let q = Point::new(Fp::new([qx0, qx1, qx2]), Fp::new([qy0, qy1, qy2]));
    ecdsa_verify(q, Fq::new([r0, r1, r2]), Fq::new([s0, s1, s2]), Fq::new([e0, e1, e2]));
}
