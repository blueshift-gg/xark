//! AES-256-CTR over an arbitrary-length message — the 256-bit-key counter mode.
//! Same structure as `examples/aes_ctr` (AES-128-CTR); the block cipher is AES-256
//! (14 rounds, 32-byte key). The 20-byte message spans two blocks (16 + a 4-byte
//! tail) to exercise the partial-final-block path.
#![cfg_attr(xark, no_std)]

use xark_aes::prelude::*;

#[circuit]
pub fn aes256_ctr(
    msg: Private<[u8; 20]>,
    key: Private<[u8; 32]>,
    nonce: Private<[u8; 12]>,
    ct: Public<[u8; 20]>,
) {
    // Qualified call: the entry fn shares the gadget's name.
    let out = xark_aes::aes256_ctr::<20>(msg, key, nonce);
    let mut i = 0usize;
    while i < 20usize {
        require_eq(out[i], ct[i]);
        i += 1;
    }
}

#[cfg(test)]
mod tests {
    use super::aes256_ctr;
    use aes_ref::cipher::generic_array::GenericArray;
    use aes_ref::cipher::{BlockEncrypt, KeyInit};
    use aes_ref::Aes256;

    const N: usize = 20;

    /// Reference AES-256-CTR: keystream block `b` = `AES256_enc(key, nonce ‖ be_u32(b))`.
    fn ctr(msg: &[u8; N], key: &[u8; 32], nonce: &[u8; 12]) -> [u8; N] {
        let cipher = Aes256::new(GenericArray::from_slice(key));
        let mut out = [0u8; N];
        let mut b = 0usize;
        while b * 16 < N {
            let mut block = [0u8; 16];
            block[0..12].copy_from_slice(nonce);
            block[12..16].copy_from_slice(&(b as u32).to_be_bytes());
            let mut ks = GenericArray::clone_from_slice(&block);
            cipher.encrypt_block(&mut ks);
            let mut j = 0usize;
            while j < 16 && b * 16 + j < N {
                out[b * 16 + j] = msg[b * 16 + j] ^ ks[j];
                j += 1;
            }
            b += 1;
        }
        out
    }

    const MSG: [u8; N] = *b"hello ctr mode world";
    const KEY: [u8; 32] = [
        0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e,
        0x0f, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d,
        0x1e, 0x1f,
    ];
    const NONCE: [u8; 12] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11];

    #[test]
    fn accepts_valid() {
        let ct = ctr(&MSG, &KEY, &NONCE);
        aes256_ctr(MSG, KEY, NONCE, ct).unwrap();
    }

    #[test]
    fn rejects_wrong_ciphertext() {
        let mut ct = ctr(&MSG, &KEY, &NONCE);
        ct[19] ^= 1;
        assert!(aes256_ctr(MSG, KEY, NONCE, ct).is_err());
    }
}
