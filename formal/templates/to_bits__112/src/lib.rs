use xark::{Field, Private, circuit};

/// The `to_bits__112` harness on fresh inputs.
#[circuit]
pub fn to_bits(x: Private<Field>) {
    let _ = x.to_bits::<112>();
}
