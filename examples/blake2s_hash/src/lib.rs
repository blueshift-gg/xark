//! Demo circuit: prove knowledge of a 100-byte message whose variable-length
//! unkeyed BLAKE2s-256 hash equals a public 8-word (256-bit) digest.
//!
//! The 100 message bytes `msg[0..100]` are the private witness (each
//! range-checked to 0..256 inside the gadget); `d[0..8]` are the public expected
//! digest words, each the LE-`u32` of 4 digest bytes. 100 bytes spans two 64-byte
//! compression blocks, exercising the Merkle-Damgard chain in
//! [`xark_blake2s::blake2s`].

#![no_std]

use xark_blake2s::blake2s;
use xark::{assert_eq, Field, Private, Public};

pub fn circuit(msg: Private<[Field; 100]>, d: Public<[Field; 8]>) {
    let hash = blake2s::<100>(msg);

    // Constrain each digest word (recomposed from its 32 bits) against the public
    // expected word. A whole inner word can't be read out of `hash`, so extract
    // it bit-by-bit into a flat local first.
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
