use xark::{Field, Private, circuit};

/// `xark_bignum::ec_add_k1_check` on fresh limbs.
#[circuit]
#[allow(clippy::too_many_arguments)]
pub fn ec_add_k1_check(
    px: Private<[Field; 8]>,
    py: Private<[Field; 8]>,
    qx: Private<[Field; 8]>,
    qy: Private<[Field; 8]>,
    w: Private<[Field; 8]>,
    lam: Private<[Field; 8]>,
    x3: Private<[Field; 8]>,
    y3: Private<[Field; 8]>,
) {
    xark_bignum::ec_add_k1_check(px, py, qx, qy, w, lam, x3, y3);
}
