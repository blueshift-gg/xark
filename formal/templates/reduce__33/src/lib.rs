use xark::{Field, Private, circuit};

/// `xark_bits::reduce::<33>` on a fresh variable.
#[circuit]
pub fn reduce(sum: Private<Field>) {
    let _ = xark_bits::reduce::<33>(sum);
}
