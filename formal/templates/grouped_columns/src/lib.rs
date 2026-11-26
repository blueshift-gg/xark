use xark::{Field, Private, circuit};

/// One 25×82 carry/telescope chain on fresh inputs.
#[circuit]
pub fn grouped_columns(
    a: Private<[Field; 25]>,
    b: Private<[Field; 25]>,
    m: Private<[Field; 25]>,
    q: Private<[Field; 25]>,
    rhs_extra: Private<[Field; 25]>,
) {
    xark_rsa::grouped_columns(a, b, m, q, rhs_extra);
}
