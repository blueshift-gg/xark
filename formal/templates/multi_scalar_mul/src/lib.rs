use xark::{Field, Private, circuit};

/// `xark_grumpkin::multi_scalar_mul` on fresh scalars and fresh points.
#[circuit]
pub fn multi_scalar_mul(scalars: Private<[Field; 2]>, points: Private<[[Field; 2]; 2]>) {
    xark_grumpkin::multi_scalar_mul(scalars, points);
}
