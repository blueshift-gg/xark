use xark::{Field, Private, circuit};

/// `xark_bignum::scalar_to_bits` on fresh limbs.
#[circuit]
pub fn scalar_to_bits(u: Private<[Field; 3]>) {
    let _ = xark_bignum::scalar_to_bits(u);
}
