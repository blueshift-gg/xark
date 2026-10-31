use xark::{Private, circuit};
use xark_grumpkin::{Affine, WideScalar};

/// `xark_grumpkin::wide_scalar_mul` on a fresh scalar and a fresh point.
#[circuit]
pub fn wide_scalar_mul(s: Private<WideScalar>, p: Private<Affine>) {
    xark_grumpkin::wide_scalar_mul(s, p);
}
