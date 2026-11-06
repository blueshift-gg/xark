use xark::{Field, Private, circuit};

/// `xark_aes::sbox` on fresh bits.
#[circuit]
pub fn sbox(bits: Private<[Field; 8]>) {
    let _ = xark_aes::sbox(bits);
}
