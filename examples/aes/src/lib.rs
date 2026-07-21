//! AES-128 single-block encryption: prove a private 16-byte plaintext and key
//! encrypt to the public ciphertext. Bytes are range-checked by `to_bits8`; the
//! S-box uses the GF(2^8) inverse `b^254` (Itoh–Tsujii) + affine map. See `xark_aes`.
#![cfg_attr(xark, no_std)]

use xark_aes::prelude::*;

#[circuit]
pub fn aes(pt: Private<[u8; 16]>, key: Private<[u8; 16]>, ct: Public<[u8; 16]>) {
    aes128_constrain(pt, key, ct);
}

#[cfg(test)]
mod tests {
    use super::aes;
    use aes_ref::cipher::generic_array::GenericArray;
    use aes_ref::cipher::{BlockEncrypt, KeyInit};
    use aes_ref::Aes128;

    fn encrypt(pt: [u8; 16], key: [u8; 16]) -> [u8; 16] {
        let cipher = Aes128::new(GenericArray::from_slice(&key));
        let mut block = GenericArray::clone_from_slice(&pt);
        cipher.encrypt_block(&mut block);
        block.into()
    }

    // FIPS-197 Appendix C.1 known-answer vector.
    const KEY: [u8; 16] = [
        0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e,
        0x0f,
    ];
    const PT: [u8; 16] = [
        0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd, 0xee,
        0xff,
    ];

    #[test]
    fn accepts_valid() {
        let ct = encrypt(PT, KEY);
        aes(PT, KEY, ct).unwrap();
    }

    #[test]
    fn rejects_wrong_ciphertext() {
        let mut ct = encrypt(PT, KEY);
        ct[0] ^= 1;
        assert!(aes(PT, KEY, ct).is_err());
    }
}
