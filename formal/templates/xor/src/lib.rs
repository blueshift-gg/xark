use xark::{Field, Private, circuit};

/// `Field::xor` on two fresh variables.
#[circuit]
pub fn xor(a: Private<Field>, b: Private<Field>) {
    let _ = a.xor(b);
}
