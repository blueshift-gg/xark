//! Demo circuit: prove knowledge of a 2-word preimage whose SHA-256 single-block
//! compression (from the standard IV, remaining message words zero) equals a
//! public 8-word digest.
//!
//! The message block is `[m[0], m[1], 0, 0, ..., 0]` (16 words). `m[0]`/`m[1]`
//! are the private witness; `d[0..8]` are the public expected output hash words.
//! Each is a 32-bit value carried as a single `Field` (decomposed to bits inside
//! the circuit).
//!
//! NOTE: this is a *single-block* compression with no length padding, so the
//! digest it constrains is the raw compression output — it is a structural demo,
//! not a spec-compliant "SHA-256 of a 2-word message".

#![no_std]

use xark_sha256::prelude::*;

pub fn circuit(m: Private<[Field; 2]>, d: Public<[Field; 8]>) {
    // Build the 16-word message block: first two words are the private inputs
    // (decomposed to bits), the remaining 14 words are constant zero. A
    // constant-zero word is 32 constant-zero bits (no advice, no gates).
    let zero = [Field::constant("0"); 32];
    let mut w = [zero; 16];
    // Write the two message words bit-by-bit (scalar slot writes: the nested
    // array store the circuit subset supports).
    let b0 = m[0].to_bits::<32>();
    let mut j = 0usize;
    while j < 32usize {
        w[0][j] = b0[j];
        j += 1;
    }
    let b1 = m[1].to_bits::<32>();
    let mut j = 0usize;
    while j < 32usize {
        w[1][j] = b1[j];
        j += 1;
    }

    // Run one SHA-256 compression from the standard IV H0.
    let hash = sha256_block(w);

    // Constrain each output word (recomposed to a field element) against the
    // corresponding public digest word. Reading `hash[i]` as a whole word isn't
    // supported, so extract each word bit-by-bit (scalar reads) into a flat
    // local first, then compare.
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
