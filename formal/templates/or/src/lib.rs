use xark::{Field, Private, circuit};

/// `Field::or` on two fresh variables.
#[circuit]
pub fn or(a: Private<Field>, b: Private<Field>) {
    let _ = a.or(b);
}
