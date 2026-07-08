//! Demo circuit: prove knowledge of a 16-word (≤64-byte) message block whose
//! BLAKE3 single-chunk root hash equals a public 8-word (256-bit) digest.
//!
//! The 16 message words `m[0..16]` are the private witness; `len` is the message
//! length in bytes (0..=64) and `d[0..8]` are the public expected digest words.
//! Each message/digest word is a 32-bit value carried as a single `Field` and
//! decomposed to bits inside the circuit (which also range-checks it < 2^32).
//!
//! BLAKE3 reads message bytes little-endian, so word `i` is the LE-`u32` value of
//! message bytes `4i..4i+4`; the digest words are likewise LE-`u32` of the digest
//! bytes `4i..4i+4`. For inputs of 0..=64 bytes this is spec-compliant BLAKE3.

#![no_std]

use xark_blake3::blake3_hash_one_block;
use xark::{assert_eq, Field, Private, Public};

pub fn circuit(m: Private<[Field; 16]>, len: Public<Field>, d: Public<[Field; 8]>) {
    // Assemble the 16-word message block, decomposing each word to bits (scalar
    // slot writes — the nested-array store the circuit subset supports).
    let zero = [Field::constant("0"); 32];
    let mut w = [zero; 16];
    let mut i = 0usize;
    while i < 16usize {
        let bits = m[i].to_bits::<32>();
        let mut j = 0usize;
        while j < 32usize {
            w[i][j] = bits[j];
            j += 1;
        }
        i += 1;
    }

    // Run the single-block BLAKE3 root hash.
    let hash = blake3_hash_one_block(w, len);

    // Constrain each output word (recomposed to a field element) against the
    // corresponding public digest word. Reading `hash[i]` as a whole word isn't
    // supported, so extract each word bit-by-bit into a flat local first.
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
