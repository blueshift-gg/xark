use xark::{Field, Private, circuit};

/// `xark_bignum::on_curve_k1_check` on fresh limbs.
#[circuit]
pub fn on_curve_k1_check(
    x: Private<[Field; 8]>,
    y: Private<[Field; 8]>,
    s: Private<[Field; 8]>,
    z: Private<[Field; 8]>,
) {
    xark_bignum::on_curve_k1_check(x, y, s, z);
}
