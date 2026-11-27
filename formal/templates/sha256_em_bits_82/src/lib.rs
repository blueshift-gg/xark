use xark::{Field, Private, circuit};

/// The encoded message's 82-bit limbs from fresh digest bits.
#[circuit]
pub fn sha256_em_bits_82(bits: Private<[Field; 256]>) {
    xark_rsa::sha256_em_bits_82(bits);
}
