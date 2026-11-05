use xark::{Field, Private, circuit};

/// `xark_bignum::mul_cert_k1` on fresh limbs `a`, `b`, `t`.
#[circuit]
pub fn mul_cert_k1(a: Private<[Field; 8]>, b: Private<[Field; 8]>, t: Private<[Field; 8]>) {
    xark_bignum::mul_cert_k1(a, b, t);
}
