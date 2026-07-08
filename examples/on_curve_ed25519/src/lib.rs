#![no_std]

//! Assert an Ed25519 point `q = (x, y)` lies on the twisted-Edwards curve
//! `−x² + y² = 1 + d·x²·y²`. This is the `enforce_on_curve` check `eddsa_verify`
//! now runs on its `A` and `R` point inputs.

use xark::{Field, Private};
use xark_ed25519::{enforce_on_curve, Fp, Point};

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
