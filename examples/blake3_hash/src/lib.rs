//! Demo circuit: prove knowledge of a 100-byte message whose variable-length
//! single-chunk BLAKE3 hash equals a public 8-word (256-bit) digest.
//!
//! Unlike `examples/blake3` (which takes 16 pre-packed 32-bit words for a single
//! ≤64-byte block), this uses [`xark_blake3::blake3`], which takes the message as
//! a byte array `[Field; N_BYTES]` and chains [`xark_blake3::compress`] across as
//! many 64-byte blocks as the length needs (here 100 bytes = 2 blocks). Each byte
//! is range-checked `< 256` and packed little-endian into the block words.
//!
//! `msg[0..100]` are the private message bytes; `d[0..8]` are the public expected
//! digest words (LE-`u32` of digest bytes `4i..4i+4`).

#![no_std]

use xark_blake3::blake3;
use xark::{assert_eq, Field, Private, Public};

pub fn circuit(msg: Private<[Field; 100]>, d: Public<[Field; 8]>) {
    let hash = blake3::<100>(msg);

    // Constrain each output word (recomposed to a field element) against the
    // corresponding public digest word. Reading a whole `hash[i]` word isn't
    // supported, so extract each word bit-by-bit into a flat local first.
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
