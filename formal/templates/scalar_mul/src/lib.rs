use xark::{Field, Private, circuit};

/// `xark_grumpkin::scalar_mul` on fresh bits and a fresh point.
#[circuit]
pub fn scalar_mul(bits: Private<[Field; 128]>, p: Private<[Field; 2]>) {
    xark_grumpkin::scalar_mul(bits, p);
}
