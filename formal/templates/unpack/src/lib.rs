use xark::{Field, Private, circuit};

/// `xark_secp256k1::unpack` on fresh halves.
#[circuit]
pub fn unpack(packed: Private<[Field; 2]>) {
    let _ = xark_secp256k1::unpack(packed);
}
