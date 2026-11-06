use xark::{Field, Private, circuit};

/// `xark_bits::add32` on two words of fresh variables.
#[circuit]
pub fn add32(a: Private<[Field; 32]>, b: Private<[Field; 32]>) {
    xark_bits::add32(a, b);
}
