//! Ergonomics demo: "hash bytes, then assert the digest equals a known value."
//!
//! This is the whole point of [`xark::Digest`]. Consuming a SHA-256 output used
//! to require reproducing the gadget's word/byte/bit layout by hand (big-endian
//! bytes within each 32-bit word, LSB-first bits within each byte) and looping an
//! element-wise `assert_eq` over 8 recomposed words. With `Digest` the circuit is
//! three lines: wrap the known hash as a constant digest, wrap the gadget output,
//! and `assert_eq` the two.
//!
//! Here the prover proves knowledge of a 3-byte private preimage whose full
//! (padded, spec-compliant) SHA-256 equals the baked-in constant
//! `sha256("abc")`. Feed `msg = [97, 98, 99]` (`"abc"`) and it verifies.

#![no_std]

use xark_sha256::prelude::*;
use xark::Digest;

/// The known digest: `sha256("abc")`, standard big-endian hex, one byte per entry.
/// `ba7816bf 8f01cfea 414140de 5dae2223 b00361a3 96177a9c b410ff61 f20015ad`.
const SHA256_ABC: [u8; 32] = [
    0xba, 0x78, 0x16, 0xbf, 0x8f, 0x01, 0xcf, 0xea, 0x41, 0x41, 0x40, 0xde, 0x5d, 0xae, 0x22, 0x23,
    0xb0, 0x03, 0x61, 0xa3, 0x96, 0x17, 0x7a, 0x9c, 0xb4, 0x10, 0xff, 0x61, 0xf2, 0x00, 0x15, 0xad,
];

pub fn circuit(msg: Private<[Field; 3]>) {
    let expected: Digest = SHA256_ABC.into();
    Digest::from(sha256(msg)).assert_eq(expected);
}
