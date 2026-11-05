use xark::{Field, Private, circuit};

/// `xark_secp256k1::unpack8` on fresh halves.
#[circuit]
pub fn unpack8_k1(packed: Private<[Field; 2]>) {
    let _ = xark_secp256k1::unpack8(packed);
}
