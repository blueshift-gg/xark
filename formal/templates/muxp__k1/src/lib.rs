use xark::{Field, Private, circuit};

/// `xark_secp256k1::muxp` on fresh inputs.
#[circuit]
pub fn muxp_k1(s: Private<Field>, a: Private<[[Field; 8]; 2]>, b: Private<[[Field; 8]; 2]>) {
    let _ = xark_secp256k1::muxp(s, a, b);
}
