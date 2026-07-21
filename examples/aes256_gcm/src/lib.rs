//! AES-256-GCM with AAD (TLS's `AES_256_GCM` suite): prove a private plaintext
//! encrypts, under a private 32-byte key + 96-bit nonce, to a public
//! `(ciphertext, tag)` that also authenticates a public 13-byte header. Identical
//! structure to `examples/aes_gcm`, but AES-256 (14 rounds, 32-byte key).
#![cfg_attr(xark, no_std)]

use xark_aes::prelude::*;

#[circuit]
pub fn aes256_gcm(
    aad: Public<[u8; 13]>,
    pt: Private<[u8; 20]>,
    key: Private<[u8; 32]>,
    nonce: Private<[u8; 12]>,
    ct: Public<[u8; 20]>,
    tag: Public<[u8; 16]>,
) {
    // Qualified call: the entry fn shares the gadget's name.
    let (c, t) = xark_aes::aes256_gcm::<13, 20>(aad, pt, key, nonce);
    require_eq(c, ct);
    require_eq(t, tag);
}

#[cfg(test)]
mod tests {
    use super::aes256_gcm;
    use aesgcm_ref::aead::{Aead, KeyInit, Payload};
    use aesgcm_ref::{Aes256Gcm, Key, Nonce};

    const AAD: [u8; 13] = *b"tls-header-13";
    const MSG: [u8; 20] = *b"authenticated data!!";
    const KEY: [u8; 32] = [
        0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e,
        0x0f, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d,
        0x1e, 0x1f,
    ];
    const NONCE: [u8; 12] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11];

    fn gcm() -> ([u8; 20], [u8; 16]) {
        let cipher = Aes256Gcm::new(Key::<Aes256Gcm>::from_slice(&KEY));
        let res = cipher
            .encrypt(
                Nonce::from_slice(&NONCE),
                Payload {
                    msg: &MSG,
                    aad: &AAD,
                },
            )
            .unwrap();
        (
            res[0..20].try_into().unwrap(),
            res[20..36].try_into().unwrap(),
        )
    }

    #[test]
    fn accepts_valid() {
        let (ct, tag) = gcm();
        aes256_gcm(AAD, MSG, KEY, NONCE, ct, tag).unwrap();
    }

    #[test]
    fn rejects_wrong_tag() {
        let (ct, mut tag) = gcm();
        tag[0] ^= 1;
        assert!(aes256_gcm(AAD, MSG, KEY, NONCE, ct, tag).is_err());
    }
}
