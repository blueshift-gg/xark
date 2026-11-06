use xark::{Field, Private, circuit};

/// `xark_merkle::cond_swap` on fresh variables.
#[circuit]
pub fn cond_swap(bit: Private<Field>, a: Private<Field>, b: Private<Field>) {
    xark_merkle::cond_swap(bit, a, b);
}
