//! AES-128-GCM with AAD: prove a private plaintext encrypts, under a private key +
//! 96-bit nonce, to a public `(ciphertext, tag)` that also authenticates a public
//! 13-byte header. GCM = AES-CTR (confidentiality) + GHASH, a GF(2¹²⁸)
//! multiply-accumulate (authentication) — the AEAD used by TLS 1.2/1.3. The 20-byte
//! message and 13-byte partial-block AAD exercise both GHASH zero-padding paths.
#![cfg_attr(xark, no_std)]

use xark_aes::prelude::*;

#[circuit]
pub fn aes_gcm(
    aad: Public<[u8; 13]>, // e.g. a record header — authenticated, not secret
    pt: Private<[u8; 20]>,
    key: Private<[u8; 16]>,
    nonce: Private<[u8; 12]>,
    ct: Public<[u8; 20]>,
    tag: Public<[u8; 16]>,
) {
    let (c, t) = aes128_gcm::<13, 20>(aad, pt, key, nonce);
    require_eq(c, ct);
    require_eq(t, tag);
}

#[cfg(test)]
mod tests {
    use super::aes_gcm;
    use aesgcm_ref::aead::{Aead, KeyInit, Payload};
    use aesgcm_ref::{Aes128Gcm, Key, Nonce};

    const AAD: [u8; 13] = *b"tls-header-13";
    const MSG: [u8; 20] = *b"authenticated data!!";
    const KEY: [u8; 16] = [
        0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e,
        0x0f,
    ];
    const NONCE: [u8; 12] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11];

    /// Reference AES-128-GCM with AAD: `encrypt(Payload{msg, aad})` returns
    /// `ciphertext ‖ tag`.
    fn gcm() -> ([u8; 20], [u8; 16]) {
        let cipher = Aes128Gcm::new(Key::<Aes128Gcm>::from_slice(&KEY));
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
        aes_gcm(AAD, MSG, KEY, NONCE, ct, tag).unwrap();
    }

    #[test]
    fn rejects_wrong_tag() {
        let (ct, mut tag) = gcm();
        tag[0] ^= 1;
        assert!(aes_gcm(AAD, MSG, KEY, NONCE, ct, tag).is_err());
    }

    #[test]
    fn rejects_tampered_aad() {
        // Same ciphertext + tag, but a flipped AAD byte must fail authentication.
        let (ct, tag) = gcm();
        let mut aad = AAD;
        aad[0] ^= 1;
        assert!(aes_gcm(aad, MSG, KEY, NONCE, ct, tag).is_err());
    }
}
