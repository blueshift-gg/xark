use xark::{Field, Private, circuit};

/// `xark_secp256r1::unpack8` on fresh halves.
#[circuit]
pub fn unpack8_r1(packed: Private<[Field; 2]>) {
    let _ = xark_secp256r1::unpack8(packed);
}
