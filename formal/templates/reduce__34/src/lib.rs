use xark::{Field, Private, circuit};

/// `xark_bits::reduce::<34>` on a fresh variable.
#[circuit]
pub fn reduce(sum: Private<Field>) {
    let _ = xark_bits::reduce::<34>(sum);
}
