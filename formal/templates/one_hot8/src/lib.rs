use xark::{Field, Private, circuit};

/// `xark_bignum::one_hot8` on fresh bits.
#[circuit]
pub fn one_hot8(bits: Private<[Field; 8]>) {
    let _ = xark_bignum::one_hot8(bits);
}
