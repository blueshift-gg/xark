//! Demo circuit: prove knowledge of an 8-byte preimage whose full (padded,
//! spec-compliant) SHA-256 equals a public 256-bit digest.
//!
//! Unlike the `sha256` example (a single-block *compression* with no padding),
//! this uses `xark_sha256::sha256::<N_BYTES>`, the Merkle–Damgård variable-length
//! hash: it appends the `0x80` delimiter, zero padding, and the 64-bit big-endian
//! bit length, then chains `compress` over every 64-byte block. So the digest it
//! constrains is a real `SHA-256(message)`.
//!
//! Layout: `msg[0..8]` are the 8 private message bytes (each range-checked to
//! `0..=255` inside the gadget); `d[0..8]` are the public expected digest words
//! (each a 32-bit big-endian slice of the 256-bit hash, carried as one `Field`).
//!
//! An 8-byte message needs a single padded block. To hash a different length,
//! change `N_BYTES` and the array length — the block count and padding are
//! resolved at compile time from the constant.

#![no_std]

use xark::{assert_eq, Field, Private, Public};
use xark_sha256::sha256;

/// The message length in bytes (compile-time constant: a circuit is fixed-size).
const N_BYTES: usize = 8;

pub fn circuit(msg: Private<[Field; N_BYTES]>, d: Public<[Field; 8]>) {
    // Full variable-length SHA-256 (padding + Merkle–Damgård chaining).
    let hash = sha256::<N_BYTES>(msg);

    // Constrain each 32-bit output word (recomposed to a field element) against
    // the corresponding public digest word. Reading `hash[i]` as a whole word
    // isn't supported, so copy each word out bit-by-bit into a flat local first.
    let zero = [Field::from(0u8); 32];
    let mut i = 0usize;
    while i < 8usize {
        let mut word = zero;
        let mut j = 0usize;
        while j < 32usize {
            word[j] = hash[i][j];
            j += 1;
        }
        assert_eq(Field::from_bits::<32>(word), d[i]);
        i += 1;
    }
}
