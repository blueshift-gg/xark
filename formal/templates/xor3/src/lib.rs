use xark::{Field, Private, circuit};

/// `xark_bits::xor3` on three fresh variables.
#[circuit]
pub fn xor3(a: Private<Field>, b: Private<Field>, c: Private<Field>) {
    let _ = xark_bits::xor3(a, b, c);
}
