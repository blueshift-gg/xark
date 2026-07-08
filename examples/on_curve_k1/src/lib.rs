#![no_std]

//! Assert a secp256k1 point `q = (x, y)` lies on the curve `y² = x³ + 7`. This
//! is the standalone `enforce_on_curve` check the ECDSA gadget now runs on its
//! public-key input: an off-curve point makes the circuit unsatisfiable.

use xark::{Field, Private};
use xark_secp256k1::{enforce_on_curve, Fp, Point};

pub fn circuit(
    qx0: Private<Field>,
    qx1: Private<Field>,
    qx2: Private<Field>,
    qy0: Private<Field>,
    qy1: Private<Field>,
    qy2: Private<Field>,
) {
    let q = Point::new(Fp::new([qx0, qx1, qx2]), Fp::new([qy0, qy1, qy2]));
    enforce_on_curve(q);
}
