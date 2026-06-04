// AES-128 CBC encryption of a 16-byte plaintext. Exercises Noir's
// `BlackBoxFuncCall::AES128Encrypt` opcode end-to-end (ROADMAP step WS-D.7).
//
// Noir's `std::aes128::aes128_encrypt` wraps the opcode and applies PKCS#7
// padding; for a 16-byte input the output is 32 bytes (one block of
// plaintext + one block of all-`0x10` padding bytes).
//
// Plaintext, IV, and key are private; the expected ciphertext is public and
// asserted byte-by-byte against the in-circuit encryption output.
use std::aes128::aes128_encrypt;

fn main(plaintext: [u8; 16], iv: [u8; 16], key: [u8; 16], ciphertext: pub [u8; 32]) {
    let c = aes128_encrypt(plaintext, iv, key);
    for i in 0..32 {
        assert(c[i] == ciphertext[i]);
    }
}
