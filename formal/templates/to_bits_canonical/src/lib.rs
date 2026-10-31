use xark::{Field, Private, circuit};

/// `Field::to_bits_canonical` on a fresh variable.
#[circuit]
pub fn to_bits_canonical(x: Private<Field>) {
    let _ = x.to_bits_canonical();
}
