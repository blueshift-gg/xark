//! AES-128-CTR over an arbitrary-length message: prove a private plaintext
//! encrypts (under a private key + 96-bit nonce) to a public ciphertext. CTR is a
//! stream cipher: keystream = `AES_enc(key, nonce ‖ be_u32(block))`, ciphertext =
//! `msg XOR keystream`. The 20-byte message spans two blocks (16 + a 4-byte tail)
//! to exercise the partial-final-block path.

use xark_aes::prelude::*;

// `#[circuit]` requires integer-literal array lengths (no `const` paths in the signature).
#[circuit]
pub fn aes_ctr(
    msg: Private<[u8; 20]>,
    key: Private<[u8; 16]>,
    nonce: Private<[u8; 12]>,
    ct: Public<[u8; 20]>,
) {
    let out = aes128_ctr::<20>(msg, key, nonce);
    require_eq(out, ct);
}

#[cfg(test)]
mod tests {
    use super::aes_ctr;
    use aes_ref::cipher::generic_array::GenericArray;

    const N: usize = 20;
    use aes_ref::cipher::{BlockEncrypt, KeyInit};
    use aes_ref::Aes128;

    /// Reference AES-128-CTR: keystream block `b` = `AES_enc(key, nonce ‖ be_u32(b))`,
    /// ciphertext = `msg XOR keystream` (the gadget's exact construction).
    fn ctr(msg: &[u8; N], key: &[u8; 16], nonce: &[u8; 12]) -> [u8; N] {
        let cipher = Aes128::new(GenericArray::from_slice(key));
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
    const KEY: [u8; 16] = [
        0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e,
        0x0f,
    ];
    const NONCE: [u8; 12] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11];

    #[test]
    fn accepts_valid() {
        let ct = ctr(&MSG, &KEY, &NONCE);
        aes_ctr(MSG, KEY, NONCE, ct).unwrap();
    }

    #[test]
    fn rejects_wrong_ciphertext() {
        let mut ct = ctr(&MSG, &KEY, &NONCE);
        ct[19] ^= 1; // flip a byte in the partial final block
        assert!(aes_ctr(MSG, KEY, NONCE, ct).is_err());
    }
}
