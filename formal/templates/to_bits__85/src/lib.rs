use xark::{Field, Private, circuit};

/// `Field::to_bits::<85>` on a fresh variable.
#[circuit]
pub fn to_bits(x: Private<Field>) {
    let _ = x.to_bits::<85>();
}
