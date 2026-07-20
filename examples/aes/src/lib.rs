//! AES-128 single-block encryption circuit.
//!
//! Proves knowledge of a 16-byte plaintext and 16-byte key whose AES-128
//! encryption equals the public 16-byte ciphertext. All 48 inputs are `Field`
//! bytes in `[0, 256)` (range-checked by `to_bits8` inside the gadget).
//!
//! S-box approach: GF(2^8) multiplicative inverse via `b^254` (Itoh–Tsujii
//! addition chain), then the fixed GF(2)-affine map + `0x63`. See `xark_aes`.
#![no_std]

use xark_aes::prelude::*;

pub fn circuit(
    pt: Private<[Field; 16]>,
    key: Private<[Field; 16]>,
    ct: Public<[Field; 16]>,
) {
    aes128_constrain(pt, key, ct);
}
