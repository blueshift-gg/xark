use xark::{Field, Private, circuit};

/// `xark_bits::chi` on three fresh variables.
#[circuit]
pub fn chi(a: Private<Field>, b: Private<Field>, c: Private<Field>) {
    let _ = xark_bits::chi(a, b, c);
}
