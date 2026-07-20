//! Demo circuit: prove that a fixed-length 200-byte private message hashes to a
//! public 256-bit Keccak-256 (Ethereum `keccak256`) digest.
//!
//! The 200 message bytes are the private witness `msg[0..200]` (each
//! range-checked to `0..256` inside `keccak256` via `to_bits::<8>`); the 4
//! digest words `d[0..4]` are the public inputs (little-endian 64-bit lanes). A
//! 200-byte message spans 2 rate blocks (padded length 272 = 2 * 136), so the
//! sponge runs `keccak_f` twice. Lane / byte order is little-endian, matching
//! the single-block gadget and Ethereum's `keccak256`.

#![no_std]

use xark_bits::from_bits64;
use xark_keccak::prelude::*;

pub fn circuit(msg: Private<[Field; 200]>, d: Public<[Field; 4]>) {
    // Variable-length sponge: absorb (2 blocks) + squeeze 256 bits (4 lanes).
    let digest = keccak256::<200>(msg);

    // Constrain each output lane (recomposed to a field element) against the
    // public digest word. Reading `digest[i]` as a whole lane isn't supported,
    // so extract each lane bit-by-bit into a flat local first.
    let zero = [Field::from(0u8); 64];
    let mut i = 0usize;
    while i < 4usize {
        let mut lane = zero;
        let mut j = 0usize;
        while j < 64usize {
            lane[j] = digest[i][j];
            j += 1;
        }
        assert_eq(from_bits64(lane), d[i]);
        i += 1;
    }
}
