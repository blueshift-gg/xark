use xark::{Field, Private, circuit};

/// One two-column carry step of the 25×82 RSA chain on fresh inputs.
#[circuit]
pub fn grouped_column_step(
    lhs0: Private<Field>,
    lhs1: Private<Field>,
    rhs0: Private<Field>,
    rhs1: Private<Field>,
    cb_prev: Private<Field>,
) {
    let _ = xark_rsa::grouped_column_step(lhs0, lhs1, rhs0, rhs1, cb_prev);
}
