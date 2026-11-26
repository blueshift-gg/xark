use xark::{Field, Private, circuit};

/// `square_lazy`'s shape: one `a` used on both sides, so the frontend's CSE merges
/// `a i · a k` with `a k · a i`.
#[circuit]
pub fn grouped_columns_square(
    a: Private<[Field; 25]>,
    m: Private<[Field; 25]>,
    q: Private<[Field; 25]>,
    rhs_extra: Private<[Field; 25]>,
) {
    xark_rsa::grouped_columns_square(a, m, q, rhs_extra);
}
