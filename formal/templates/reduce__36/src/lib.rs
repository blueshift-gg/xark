use xark::{Field, Private, circuit};

/// `xark_bits::reduce::<36>` on a fresh variable.
#[circuit]
pub fn reduce(sum: Private<Field>) {
    let _ = xark_bits::reduce::<36>(sum);
}
