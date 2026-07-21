//! Ergonomics demo for `xark_hash::Digest`: prove knowledge of a 3-byte private
//! preimage whose SHA-256 equals the baked-in constant `sha256("abc")`. Since the
//! expected digest is a compile-time constant, the circuit has no public inputs.
#![cfg_attr(xark, no_std)]

use xark_sha256::prelude::*; // re-exports `Digest`

/// `sha256("abc")`, big-endian, one byte per entry.
const SHA256_ABC: [u8; 32] = [
    0xba, 0x78, 0x16, 0xbf, 0x8f, 0x01, 0xcf, 0xea, 0x41, 0x41, 0x40, 0xde, 0x5d, 0xae, 0x22, 0x23,
    0xb0, 0x03, 0x61, 0xa3, 0x96, 0x17, 0x7a, 0x9c, 0xb4, 0x10, 0xff, 0x61, 0xf2, 0x00, 0x15, 0xad,
];

#[circuit]
pub fn sha256_consume(msg: Private<[u8; 3]>) {
    let expected: Digest = SHA256_ABC.into();
    Digest::from(sha256(msg)).require_eq(expected);
}

#[cfg(test)]
mod tests {
    use super::sha256_consume;

    #[test]
    fn accepts_abc() {
        sha256_consume(*b"abc").unwrap();
    }

    #[test]
    fn rejects_wrong_preimage() {
        assert!(sha256_consume(*b"abd").is_err());
    }
}
