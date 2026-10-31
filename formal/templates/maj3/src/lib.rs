use xark::{Field, Private, circuit};

/// `xark_bits::maj3` on three fresh variables.
#[circuit]
pub fn maj3(a: Private<Field>, b: Private<Field>, c: Private<Field>) {
    let _ = xark_bits::maj3(a, b, c);
}
