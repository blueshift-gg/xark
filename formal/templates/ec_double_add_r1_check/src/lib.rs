use xark::{Field, Private, circuit};

/// `xark_bignum::ec_double_add_r1_check` on fresh limbs.
#[circuit]
#[allow(clippy::too_many_arguments)]
pub fn ec_double_add_r1_check(
    ax: Private<[Field; 8]>,
    ay: Private<[Field; 8]>,
    sx: Private<[Field; 8]>,
    sy: Private<[Field; 8]>,
    w: Private<[Field; 8]>,
    l1: Private<[Field; 8]>,
    xr: Private<[Field; 8]>,
    l2: Private<[Field; 8]>,
    x3: Private<[Field; 8]>,
    y3: Private<[Field; 8]>,
) {
    xark_bignum::ec_double_add_r1_check(ax, ay, sx, sy, w, l1, xr, l2, x3, y3);
}
