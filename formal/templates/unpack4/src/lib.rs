use xark::{Field, Private, circuit};

/// `xark_secp256r1::unpack4` on fresh halves.
#[circuit]
pub fn unpack4(packed: Private<[Field; 2]>) {
    let _ = xark_secp256r1::unpack4(packed);
}
