use xark::{Field, Private, circuit};

/// `xark_bits::ch` on three fresh variables.
#[circuit]
pub fn ch(a: Private<Field>, b: Private<Field>, c: Private<Field>) {
    let _ = xark_bits::ch(a, b, c);
}
