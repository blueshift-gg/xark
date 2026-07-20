//! Demo circuit: prove that a known 17-lane (already-padded) Keccak-256 rate
//! block hashes to a public 256-bit digest.
//!
//! The 17 padded block lanes are the private witness `words[0..17]`; the 4 digest
//! words `d[0..4]` are the public inputs. Each is a 64-bit value carried as a
//! single `Field` and decomposed to bits inside the circuit via
//! `xark_bits::to_bits64`. We run `keccak256_block` and constrain the 4 output
//! lanes (recomposed with `from_bits64`) against the public digest words.
//!
//! Lane / byte order is little-endian, matching Ethereum's `keccak256`. For the
//! empty message the padded block is `words[0] = 0x0000000000000001`,
//! `words[16] = 0x8000000000000000`, rest 0, and the digest is
//! `c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470`.

#![no_std]

use xark_bits::{from_bits64, to_bits64};
use xark_keccak::prelude::*;

pub fn circuit(words: Private<[Field; 17]>, d: Public<[Field; 4]>) {
    // Decompose each block word into a 64-bit lane. Each `to_bits64`
    // boolean-constrains and pins the bits to the input word (64 gates apiece),
    // so the private witness cannot cheat the lane contents.
    let zero = [Field::constant("0"); 64];
    let mut block = [zero; 17];
    let mut i = 0usize;
    while i < 17usize {
        let lane = to_bits64(words[i]);
        let mut j = 0usize;
        while j < 64usize {
            block[i][j] = lane[j];
            j += 1;
        }
        i += 1;
    }

    // Absorb one block, permute, squeeze 256 bits (4 lanes).
    let digest = keccak256_block(block);

    // Constrain each output lane (recomposed to a field element) against the
    // public digest word. Reading `digest[i]` as a whole lane isn't supported,
    // so extract each lane bit-by-bit into a flat local first.
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
