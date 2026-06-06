//! Blake3 hash gadget.
//!
//! Implements the [Blake3](https://github.com/BLAKE3-team/BLAKE3) hash on a
//! **variable-length byte input** producing a 32-byte digest. Used by Noir's
//! `BlackBoxFuncCall::Blake3`.
//!
//! ## Multi-chunk support
//!
//! Blake3 is a Merkle tree of 1024-byte chunks. Inputs ≤ 1024 bytes hit the
//! single-chunk fast path: split into ≤ 16 blocks of 64 bytes each, run the
//! compression function with flags appropriate for the first / middle / last
//! block, and return the final chaining value (with `ROOT` set on the last
//! block).
//!
//! For inputs **larger than 1024 bytes** the gadget builds the binary tree
//! by computing per-chunk chaining values (each chunk uses
//! `counter = chunk_index` and no `ROOT` flag) and combining them via
//! `PARENT` compressions. The root parent compression sets `ROOT`. Subtree
//! shapes follow the official reference: at each parent node, the left
//! subtree contains the largest power of two of full chunks present, with
//! the remainder on the right.
//!
//! ## Compression function
//!
//! Each block runs through `compress(cv, block_words, counter, block_len, flags)`:
//!
//! 1. The 16-word state `v` is initialised to
//!    `[cv[0..8], IV[0..4], counter_low, counter_high, block_len, flags]`.
//! 2. Seven rounds of mixing. Each round applies the `G` function to four
//!    columns then four diagonals; the message word ordering per round is
//!    given by the official Blake3 `MSG_SCHEDULE` table.
//! 3. The new chaining value is `cv'[i] = state[i] ^ state[i+8]` for `i ∈ 0..8`.
//!
//! The `G` mixing function is byte-for-byte the same as Blake2s — including
//! the rotation amounts (16, 12, 8, 7). The only differences vs Blake2s are
//! the round count (7 vs 10), the σ table, and the initial `v[12..16]` slots
//! (counter/block-len/flags vs Blake2s' XOR-into-IV pattern).
//!
//! ## Flags (single-chunk case)
//!
//! For the only-chunk-in-the-tree case, the per-block flags are:
//!
//! * First block of a multi-block chunk: `CHUNK_START` (`= 1`)
//! * Middle blocks: `0`
//! * Last block of the root chunk: `CHUNK_END | ROOT` (`= 10`)
//! * Single block that's also the root: `CHUNK_START | CHUNK_END | ROOT` (`= 11`)
//!
//! For empty input we still run a single compression with `block_len = 0`,
//! `flags = CHUNK_START | CHUNK_END | ROOT`, message all zeros — the official
//! Blake3 implementation handles this in its `ChunkState::finalize` path.
//!
//! ## In-circuit cost
//!
//! Each compression call has 7 rounds × 8 `G` operations = 56 `G` calls. Each
//! `G` does 4 `add_mod_32` + 4 `XOR`s. Compared to Blake2s' 80 `G` calls,
//! Blake3 is ~30 % cheaper per block.

#![allow(clippy::needless_range_loop)]

use ark_bn254::Fr;
use ark_ff::One;
use ark_relations::gr1cs::{LinearCombination, SynthesisError, Variable};

use crate::gadgets::bitwise::{Word32, add_mod_32, xor};
use crate::gadgets::range::{decompose_into_bits, enforce_recompose_equals};
use crate::r1cs_builder::R1csBuilder;

/// Blake3 initialization vector (same eight 32-bit constants as Blake2s /
/// SHA-256 — the first 32 bits of the fractional parts of the square roots
/// of the first eight primes).
pub const BLAKE3_IV: [u32; 8] = [
    0x6A09_E667,
    0xBB67_AE85,
    0x3C6E_F372,
    0xA54F_F53A,
    0x510E_527F,
    0x9B05_688C,
    0x1F83_D9AB,
    0x5BE0_CD19,
];

/// Per-round message-word permutation σ. Seven rounds, taken verbatim from the
/// Blake3 reference implementation (`MSG_SCHEDULE`).
pub const BLAKE3_MSG_SCHEDULE: [[usize; 16]; 7] = [
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    [2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8],
    [3, 4, 10, 12, 13, 2, 7, 14, 6, 5, 9, 0, 11, 15, 8, 1],
    [10, 7, 12, 9, 14, 3, 13, 15, 4, 0, 11, 2, 5, 8, 1, 6],
    [12, 13, 9, 11, 15, 10, 14, 8, 7, 2, 5, 3, 0, 1, 6, 4],
    [9, 14, 11, 5, 8, 12, 15, 1, 13, 3, 0, 10, 2, 6, 4, 7],
    [11, 15, 5, 0, 1, 9, 8, 6, 14, 10, 2, 12, 3, 4, 7, 13],
];

/// G-mixing rotation constants (identical to Blake2s).
const R1: usize = 16;
const R2: usize = 12;
const R3: usize = 8;
const R4: usize = 7;

/// Number of compression rounds.
const ROUNDS: usize = 7;

/// Block size in bytes.
const BLOCK_BYTES: usize = 64;

/// Chunk size in bytes.
pub const CHUNK_BYTES: usize = 1024;

/// Digest size in bytes.
const DIGEST_BYTES: usize = 32;

// -- Per-block flags (see Blake3 spec §2.3). -----------------------------------
const CHUNK_START: u8 = 1 << 0;
const CHUNK_END: u8 = 1 << 1;
const PARENT: u8 = 1 << 2;
const ROOT: u8 = 1 << 3;

/// Largest power of two that is less than or equal to `n` (and ≥ 1).
/// Used by the Blake3 binary tree to choose the left-subtree size.
fn largest_pow2_leq(n: usize) -> usize {
    debug_assert!(n >= 1);
    let mut x = 1usize;
    while (x * 2) <= n {
        x *= 2;
    }
    x
}

/// Number of chunks the left subtree should contain when combining
/// `total_chunks` chunks at a parent node. Per the Blake3 reference, the
/// left subtree gets the largest power of two of the full chunks present
/// (the "-1" reserves at least one byte / chunk for the right side).
fn left_subtree_chunks(total_chunks: usize) -> usize {
    debug_assert!(total_chunks >= 2);
    // Treat the last chunk as "potentially partial"; the remaining
    // `total_chunks - 1` are full and feed into the power-of-2 calculation.
    let full = total_chunks - 1;
    largest_pow2_leq(full)
}

// =============================================================================
// Native reference
// =============================================================================

/// Native Blake3 with full multi-chunk support. Used by the gadget at proving
/// time (for known intermediate values) and by the KAT tests.
pub fn blake3_native(input: &[u8]) -> [u8; 32] {
    let n = input.len();
    if n <= CHUNK_BYTES {
        // Single-chunk fast path: the chunk's last block IS the root.
        return chunk_compress_native(input, 0, true).digest_bytes();
    }

    // -- Multi-chunk: 1) compute chunk CVs, 2) combine via binary tree. ----
    let num_chunks = n.div_ceil(CHUNK_BYTES);
    let mut chunk_cvs: Vec<[u32; 8]> = Vec::with_capacity(num_chunks);
    for i in 0..num_chunks {
        let start = i * CHUNK_BYTES;
        let end = (start + CHUNK_BYTES).min(n);
        chunk_cvs.push(chunk_compress_native(&input[start..end], i as u64, false).cv);
    }
    let root_cv = combine_chunks_native(&chunk_cvs, true);
    cv_to_digest_bytes(&root_cv)
}

/// Result of running one Blake3 chunk: the final CV (8 LE u32 words) plus the
/// optional full 16-word post-state — for the single-chunk-root case we
/// already have the digest bytes, but every other caller only needs `cv`.
#[derive(Clone)]
struct ChunkResult {
    cv: [u32; 8],
}

impl ChunkResult {
    fn digest_bytes(&self) -> [u8; 32] {
        cv_to_digest_bytes(&self.cv)
    }
}

fn cv_to_digest_bytes(cv: &[u32; 8]) -> [u8; 32] {
    let mut out = [0u8; DIGEST_BYTES];
    for (i, w) in cv.iter().enumerate() {
        out[i * 4..i * 4 + 4].copy_from_slice(&w.to_le_bytes());
    }
    out
}

/// Process a single chunk's blocks. `chunk_data.len() ≤ CHUNK_BYTES`.
/// `chunk_counter` is the 0-indexed chunk position within the message.
/// `is_root_chunk` is `true` iff this chunk's final block should set
/// `ROOT` (single-chunk message only).
fn chunk_compress_native(
    chunk_data: &[u8],
    chunk_counter: u64,
    is_root_chunk: bool,
) -> ChunkResult {
    let n = chunk_data.len();
    let mut cv = BLAKE3_IV;
    let full_blocks = if n == 0 { 0 } else { (n - 1) / BLOCK_BYTES };
    for i in 0..full_blocks {
        let start = i * BLOCK_BYTES;
        let mut block = [0u8; BLOCK_BYTES];
        block.copy_from_slice(&chunk_data[start..start + BLOCK_BYTES]);
        let m = block_to_words(&block);
        let flags = if i == 0 { CHUNK_START } else { 0 };
        let state = compress_pre_native(&cv, &m, chunk_counter, BLOCK_BYTES as u32, flags);
        for k in 0..8 {
            cv[k] = state[k] ^ state[k + 8];
        }
    }
    let mut block = [0u8; BLOCK_BYTES];
    let tail_start = full_blocks * BLOCK_BYTES;
    let tail_len = n - tail_start;
    block[..tail_len].copy_from_slice(&chunk_data[tail_start..]);
    let m = block_to_words(&block);
    let mut flags = CHUNK_END;
    if full_blocks == 0 {
        flags |= CHUNK_START;
    }
    if is_root_chunk {
        flags |= ROOT;
    }
    let state = compress_pre_native(&cv, &m, chunk_counter, tail_len as u32, flags);
    for k in 0..8 {
        cv[k] = state[k] ^ state[k + 8];
    }
    ChunkResult { cv }
}

/// Recursively combine chunk CVs via `PARENT` compressions. The top-level
/// call passes `at_root = true` so the resulting compression sets `ROOT`.
fn combine_chunks_native(chunk_cvs: &[[u32; 8]], at_root: bool) -> [u32; 8] {
    debug_assert!(!chunk_cvs.is_empty());
    if chunk_cvs.len() == 1 {
        return chunk_cvs[0];
    }
    let split = left_subtree_chunks(chunk_cvs.len());
    let left = combine_chunks_native(&chunk_cvs[..split], false);
    let right = combine_chunks_native(&chunk_cvs[split..], false);
    parent_compress_native(&left, &right, at_root)
}

/// Parent compression: combines two child CVs into one. Uses Blake3 IV as the
/// initial chaining value, message words = `left_cv ++ right_cv`, counter = 0,
/// block_len = 64, flags = `PARENT [| ROOT]`.
fn parent_compress_native(left: &[u32; 8], right: &[u32; 8], at_root: bool) -> [u32; 8] {
    let mut m = [0u32; 16];
    m[..8].copy_from_slice(left);
    m[8..].copy_from_slice(right);
    let mut flags = PARENT;
    if at_root {
        flags |= ROOT;
    }
    let state = compress_pre_native(&BLAKE3_IV, &m, 0, BLOCK_BYTES as u32, flags);
    let mut out = [0u32; 8];
    for k in 0..8 {
        out[k] = state[k] ^ state[k + 8];
    }
    out
}

fn block_to_words(block: &[u8; BLOCK_BYTES]) -> [u32; 16] {
    let mut m = [0u32; 16];
    for j in 0..16 {
        m[j] = u32::from_le_bytes(block[j * 4..j * 4 + 4].try_into().unwrap());
    }
    m
}

/// Run the full 7-round compression and return the 16-word post-state (the
/// caller is responsible for XOR'ing halves to produce the new chaining value
/// or extended output).
fn compress_pre_native(
    cv: &[u32; 8],
    m: &[u32; 16],
    counter: u64,
    block_len: u32,
    flags: u8,
) -> [u32; 16] {
    let mut v = [
        cv[0],
        cv[1],
        cv[2],
        cv[3],
        cv[4],
        cv[5],
        cv[6],
        cv[7],
        BLAKE3_IV[0],
        BLAKE3_IV[1],
        BLAKE3_IV[2],
        BLAKE3_IV[3],
        counter as u32,
        (counter >> 32) as u32,
        block_len,
        flags as u32,
    ];
    for r in 0..ROUNDS {
        let s = &BLAKE3_MSG_SCHEDULE[r];
        mix_native(&mut v, 0, 4, 8, 12, m[s[0]], m[s[1]]);
        mix_native(&mut v, 1, 5, 9, 13, m[s[2]], m[s[3]]);
        mix_native(&mut v, 2, 6, 10, 14, m[s[4]], m[s[5]]);
        mix_native(&mut v, 3, 7, 11, 15, m[s[6]], m[s[7]]);

        mix_native(&mut v, 0, 5, 10, 15, m[s[8]], m[s[9]]);
        mix_native(&mut v, 1, 6, 11, 12, m[s[10]], m[s[11]]);
        mix_native(&mut v, 2, 7, 8, 13, m[s[12]], m[s[13]]);
        mix_native(&mut v, 3, 4, 9, 14, m[s[14]], m[s[15]]);
    }
    v
}

#[inline]
fn mix_native(v: &mut [u32; 16], a: usize, b: usize, c: usize, d: usize, x: u32, y: u32) {
    v[a] = v[a].wrapping_add(v[b]).wrapping_add(x);
    v[d] = (v[d] ^ v[a]).rotate_right(R1 as u32);
    v[c] = v[c].wrapping_add(v[d]);
    v[b] = (v[b] ^ v[c]).rotate_right(R2 as u32);
    v[a] = v[a].wrapping_add(v[b]).wrapping_add(y);
    v[d] = (v[d] ^ v[a]).rotate_right(R3 as u32);
    v[c] = v[c].wrapping_add(v[d]);
    v[b] = (v[b] ^ v[c]).rotate_right(R4 as u32);
}

// =============================================================================
// In-circuit gadget
// =============================================================================

/// Run Blake3 on `input_vars` (each is a u8-valued `(Variable, Option<Fr>)`
/// pair) and return 32 freshly-allocated witness `Variable`s, one per output
/// byte, each pinned via a single linear equality to its bit decomposition.
///
/// Handles inputs of any length by building Blake3's binary Merkle tree of
/// 1024-byte chunks combined via `PARENT` compressions. Each chunk produces
/// an 8-word chaining value; pairs of CVs are reduced via parent
/// compressions until a single root CV remains, which is XOR-half'd to the
/// final 32-byte digest.
pub fn blake3_in_circuit(
    builder: &mut R1csBuilder<'_>,
    input_vars: &[(Variable, Option<Fr>)],
) -> Result<[Variable; DIGEST_BYTES], SynthesisError> {
    let n = input_vars.len();

    // -- 1. Decompose every input byte into 8 boolean wires (LSB first). -------
    let mut byte_bits: Vec<[Variable; 8]> = Vec::with_capacity(n);
    let mut byte_values: Vec<Option<u8>> = Vec::with_capacity(n);
    for (var, value) in input_vars.iter() {
        let bits = decompose_into_bits(builder, *var, 8, *value)?;
        let bits_arr: [Variable; 8] = std::array::from_fn(|i| bits[i]);
        byte_bits.push(bits_arr);
        byte_values.push(value.map(fr_to_u8_low));
    }

    // -- 2. Single-chunk fast path or multi-chunk tree. ------------------------
    let cv: [Word32; 8] = if n <= CHUNK_BYTES {
        chunk_compress_in_circuit(builder, &byte_bits, &byte_values, 0, n, 0, true)?
    } else {
        // Multi-chunk: compute per-chunk CVs, combine via binary tree.
        let num_chunks = n.div_ceil(CHUNK_BYTES);
        let mut chunk_cvs: Vec<[Word32; 8]> = Vec::with_capacity(num_chunks);
        for i in 0..num_chunks {
            let start = i * CHUNK_BYTES;
            let end = (start + CHUNK_BYTES).min(n);
            let chunk_cv = chunk_compress_in_circuit(
                builder,
                &byte_bits,
                &byte_values,
                start,
                end,
                i as u64,
                false,
            )?;
            chunk_cvs.push(chunk_cv);
        }
        combine_chunks_in_circuit(builder, &chunk_cvs, true)?
    };

    // -- 4. Output: 8 LE u32 words -> 32 bytes. --------------------------------
    let mut out_bytes = [Variable::One; DIGEST_BYTES];
    for word_idx in 0..8 {
        let word = &cv[word_idx];
        for byte_in_word in 0..4 {
            let bit_start = byte_in_word * 8;
            let byte_lcs: Vec<LinearCombination<Fr>> =
                (0..8).map(|b| word.bits[bit_start + b].clone()).collect();
            let byte_value = word.value.map(|w| ((w >> bit_start) & 0xFF) as u8);
            let byte_fr = byte_value.map(|b| Fr::from(b as u64));
            let byte_var = builder.alloc_with_value(byte_fr)?;
            enforce_recompose_equals(builder, &byte_lcs, byte_var)?;
            out_bytes[word_idx * 4 + byte_in_word] = byte_var;
        }
    }

    Ok(out_bytes)
}

/// Run one Blake3 chunk inside the circuit: produces the chunk's chaining
/// value `cv` from a 64-byte-aligned slice of the input. `chunk_byte_start`
/// and `chunk_byte_end` mark the chunk's range in the global input;
/// `chunk_counter` is the 0-indexed chunk position; `is_root_chunk` is
/// `true` only when the WHOLE message fits in this one chunk (no parent
/// compressions follow).
#[allow(clippy::too_many_arguments)]
fn chunk_compress_in_circuit(
    builder: &mut R1csBuilder<'_>,
    byte_bits: &[[Variable; 8]],
    byte_values: &[Option<u8>],
    chunk_byte_start: usize,
    chunk_byte_end: usize,
    chunk_counter: u64,
    is_root_chunk: bool,
) -> Result<[Word32; 8], SynthesisError> {
    let chunk_len = chunk_byte_end - chunk_byte_start;
    debug_assert!(chunk_len <= CHUNK_BYTES);
    let mut cv: [Word32; 8] = std::array::from_fn(|i| Word32::constant(BLAKE3_IV[i]));
    let full_blocks = if chunk_len == 0 {
        0
    } else {
        (chunk_len - 1) / BLOCK_BYTES
    };
    for block_idx in 0..full_blocks {
        let block_start = chunk_byte_start + block_idx * BLOCK_BYTES;
        let m = pack_block_message(byte_bits, byte_values, block_start, chunk_byte_end);
        let flags = if block_idx == 0 { CHUNK_START } else { 0 };
        cv = compress_in_circuit(builder, &cv, &m, chunk_counter, BLOCK_BYTES as u32, flags)?;
    }
    let tail_start = chunk_byte_start + full_blocks * BLOCK_BYTES;
    let tail_len = chunk_byte_end - tail_start;
    let m = pack_block_message(byte_bits, byte_values, tail_start, chunk_byte_end);
    let mut flags = CHUNK_END;
    if full_blocks == 0 {
        flags |= CHUNK_START;
    }
    if is_root_chunk {
        flags |= ROOT;
    }
    compress_in_circuit(builder, &cv, &m, chunk_counter, tail_len as u32, flags)
}

/// Recursively combine chunk CVs via in-circuit parent compressions. The
/// top-level invocation passes `at_root = true` so the resulting compression
/// sets the `ROOT` flag.
fn combine_chunks_in_circuit(
    builder: &mut R1csBuilder<'_>,
    chunk_cvs: &[[Word32; 8]],
    at_root: bool,
) -> Result<[Word32; 8], SynthesisError> {
    debug_assert!(!chunk_cvs.is_empty());
    if chunk_cvs.len() == 1 {
        return Ok(chunk_cvs[0].clone());
    }
    let split = left_subtree_chunks(chunk_cvs.len());
    let left = combine_chunks_in_circuit(builder, &chunk_cvs[..split], false)?;
    let right = combine_chunks_in_circuit(builder, &chunk_cvs[split..], false)?;
    parent_compress_in_circuit(builder, &left, &right, at_root)
}

/// In-circuit parent compression: message = `left_cv ++ right_cv` as 16 u32
/// words, counter = 0, block_len = 64, flags = `PARENT [| ROOT]`.
fn parent_compress_in_circuit(
    builder: &mut R1csBuilder<'_>,
    left: &[Word32; 8],
    right: &[Word32; 8],
    at_root: bool,
) -> Result<[Word32; 8], SynthesisError> {
    let m: [Word32; 16] = std::array::from_fn(|i| {
        if i < 8 {
            left[i].clone()
        } else {
            right[i - 8].clone()
        }
    });
    let mut flags = PARENT;
    if at_root {
        flags |= ROOT;
    }
    let iv_cv: [Word32; 8] = std::array::from_fn(|i| Word32::constant(BLAKE3_IV[i]));
    compress_in_circuit(builder, &iv_cv, &m, 0, BLOCK_BYTES as u32, flags)
}

/// Build the 16 32-bit message words for a single 64-byte block. Bytes past
/// the input length are zero-padded with the constant-zero LC.
fn pack_block_message(
    byte_bits: &[[Variable; 8]],
    byte_values: &[Option<u8>],
    block_start: usize,
    n: usize,
) -> [Word32; 16] {
    std::array::from_fn(|j| {
        let mut bit_lcs: Vec<LinearCombination<Fr>> = Vec::with_capacity(32);
        let mut known_value: Option<u32> = Some(0);
        for byte_in_word in 0..4 {
            let byte_idx = block_start + j * 4 + byte_in_word;
            if byte_idx < n {
                for bit in 0..8 {
                    let v = byte_bits[byte_idx][bit];
                    bit_lcs.push(LinearCombination(vec![(Fr::one(), v)]));
                }
                if let Some(b) = byte_values[byte_idx] {
                    if let Some(acc) = known_value.as_mut() {
                        *acc |= (b as u32) << (8 * byte_in_word);
                    }
                } else {
                    known_value = None;
                }
            } else {
                for _ in 0..8 {
                    bit_lcs.push(LinearCombination(vec![]));
                }
            }
        }
        Word32::from_bits(bit_lcs, known_value)
    })
}

/// One Blake3 compression. Returns the updated 8-word chaining value
/// `cv'[i] = state[i] ^ state[i+8]`.
fn compress_in_circuit(
    builder: &mut R1csBuilder<'_>,
    cv: &[Word32; 8],
    m: &[Word32; 16],
    counter: u64,
    block_len: u32,
    flags: u8,
) -> Result<[Word32; 8], SynthesisError> {
    let mut v: Vec<Word32> = Vec::with_capacity(16);
    // v[0..8] = cv
    for word in cv.iter() {
        v.push(word.clone());
    }
    // v[8..12] = IV[0..4]
    for &iv_i in BLAKE3_IV[..4].iter() {
        v.push(Word32::constant(iv_i));
    }
    // v[12] = counter_low, v[13] = counter_high, v[14] = block_len, v[15] = flags
    v.push(Word32::constant(counter as u32));
    v.push(Word32::constant((counter >> 32) as u32));
    v.push(Word32::constant(block_len));
    v.push(Word32::constant(flags as u32));

    for r in 0..ROUNDS {
        let s = &BLAKE3_MSG_SCHEDULE[r];
        mix_in_circuit(builder, &mut v, 0, 4, 8, 12, &m[s[0]], &m[s[1]])?;
        mix_in_circuit(builder, &mut v, 1, 5, 9, 13, &m[s[2]], &m[s[3]])?;
        mix_in_circuit(builder, &mut v, 2, 6, 10, 14, &m[s[4]], &m[s[5]])?;
        mix_in_circuit(builder, &mut v, 3, 7, 11, 15, &m[s[6]], &m[s[7]])?;

        mix_in_circuit(builder, &mut v, 0, 5, 10, 15, &m[s[8]], &m[s[9]])?;
        mix_in_circuit(builder, &mut v, 1, 6, 11, 12, &m[s[10]], &m[s[11]])?;
        mix_in_circuit(builder, &mut v, 2, 7, 8, 13, &m[s[12]], &m[s[13]])?;
        mix_in_circuit(builder, &mut v, 3, 4, 9, 14, &m[s[14]], &m[s[15]])?;
    }

    // cv'[i] = v[i] XOR v[i+8].
    let mut out: Vec<Word32> = Vec::with_capacity(8);
    for i in 0..8 {
        out.push(xor(builder, &v[i], &v[i + 8])?);
    }
    Ok(out.try_into().unwrap_or_else(|_| unreachable!()))
}

/// In-circuit G mixing function (identical structure to Blake2s).
#[allow(clippy::too_many_arguments)]
fn mix_in_circuit(
    builder: &mut R1csBuilder<'_>,
    v: &mut [Word32],
    a: usize,
    b: usize,
    c: usize,
    d: usize,
    x: &Word32,
    y: &Word32,
) -> Result<(), SynthesisError> {
    // v[a] = v[a] + v[b] + x
    v[a] = add_mod_32(builder, &[&v[a], &v[b], x])?;
    // v[d] = (v[d] XOR v[a]) >>> R1
    v[d] = rotr_w32(&xor(builder, &v[d], &v[a])?, R1);
    // v[c] = v[c] + v[d]
    v[c] = add_mod_32(builder, &[&v[c], &v[d]])?;
    // v[b] = (v[b] XOR v[c]) >>> R2
    v[b] = rotr_w32(&xor(builder, &v[b], &v[c])?, R2);
    // v[a] = v[a] + v[b] + y
    v[a] = add_mod_32(builder, &[&v[a], &v[b], y])?;
    // v[d] = (v[d] XOR v[a]) >>> R3
    v[d] = rotr_w32(&xor(builder, &v[d], &v[a])?, R3);
    // v[c] = v[c] + v[d]
    v[c] = add_mod_32(builder, &[&v[c], &v[d]])?;
    // v[b] = (v[b] XOR v[c]) >>> R4
    v[b] = rotr_w32(&xor(builder, &v[b], &v[c])?, R4);
    Ok(())
}

/// Right rotation of a `Word32` — thin wrapper around the bitwise helper so we
/// don't add an extra import at the call sites.
fn rotr_w32(a: &Word32, k: usize) -> Word32 {
    crate::gadgets::bitwise::rotr(a, k)
}

/// Truncate an `Fr` to its low 8 bits.
fn fr_to_u8_low(fr: Fr) -> u8 {
    let bytes = crate::field::fr_to_be_bytes(&fr);
    bytes[31]
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::witness::WitnessMap;
    use ark_relations::gr1cs::ConstraintSystem;
    use rand::Rng;
    use rand::SeedableRng;
    use rand::rngs::StdRng;

    /// Expected `blake3(b"abc")` digest from the official Blake3 spec / test
    /// vectors. Reproduced here so the native test acts as a true KAT and is
    /// independent of the `blake3` crate's own constants.
    const ABC_DIGEST_HEX: &str = "6437b3ac38465133ffb63b75273a8db548c558465d79db03fd359c6cd5bd9d85";

    fn alloc_byte(builder: &mut R1csBuilder<'_>, value: u8) -> (Variable, Option<Fr>) {
        let fr = Fr::from(value as u64);
        let v = builder.alloc_with_value(Some(fr)).unwrap();
        (v, Some(fr))
    }

    fn byte_var_value(cs: &ark_relations::gr1cs::ConstraintSystemRef<Fr>, v: Variable) -> u8 {
        let fr = cs.assigned_value(v).expect("variable has an assignment");
        fr_to_u8_low(fr)
    }

    #[test]
    fn blake3_native_matches_blake3_crate_on_abc() {
        let got = blake3_native(b"abc");
        let want: [u8; 32] = blake3::hash(b"abc").into();
        assert_eq!(got, want);
        assert_eq!(hex::encode(got), ABC_DIGEST_HEX);
    }

    #[test]
    fn blake3_native_matches_blake3_crate_random_lengths() {
        let mut rng = StdRng::seed_from_u64(0xB3_5B_25_00);
        // Cover empty, sub-block, exact-block, multi-block, and chunk-boundary
        // lengths to exercise the flag bookkeeping.
        for &len in &[
            0usize, 1, 17, 55, 63, 64, 65, 100, 128, 1023, 1024,
            // Multi-chunk regression: 2, 3, 4, 5, partial-tail, exact-boundary,
            // and several chunks crossing the 4096-byte / 8192-byte boundary.
            1025, 1500, 2048, 2049, 3000, 4096, 5000, 8192, 8193, 12000,
        ] {
            let input: Vec<u8> = (0..len).map(|_| rng.r#gen()).collect();
            let got = blake3_native(&input);
            let want: [u8; 32] = blake3::hash(&input).into();
            assert_eq!(got, want, "blake3_native mismatch at len={len}");
        }
    }

    #[test]
    fn blake3_in_circuit_matches_native_on_abc() {
        let cs = ConstraintSystem::<Fr>::new_ref();
        let map = WitnessMap::<Fr>::new();
        let mut b = R1csBuilder::new(cs.clone(), Some(&map));
        b.finish_public_pass();

        let input = b"abc";
        let in_vars: Vec<(Variable, Option<Fr>)> =
            input.iter().map(|&byte| alloc_byte(&mut b, byte)).collect();

        let out = blake3_in_circuit(&mut b, &in_vars).unwrap();

        assert!(cs.is_satisfied().unwrap(), "constraint system unsatisfied");

        let expected = blake3_native(input);
        for i in 0..DIGEST_BYTES {
            let got = byte_var_value(&cs, out[i]);
            assert_eq!(got, expected[i], "byte {i} mismatch");
        }

        println!(
            "Blake3 (3-byte input): {} constraints, {} witnesses",
            cs.num_constraints(),
            cs.num_witness_variables()
        );
    }

    #[test]
    fn blake3_in_circuit_empty_input() {
        let cs = ConstraintSystem::<Fr>::new_ref();
        let map = WitnessMap::<Fr>::new();
        let mut b = R1csBuilder::new(cs.clone(), Some(&map));
        b.finish_public_pass();

        let in_vars: Vec<(Variable, Option<Fr>)> = vec![];
        let out = blake3_in_circuit(&mut b, &in_vars).unwrap();
        assert!(cs.is_satisfied().unwrap());

        let expected = blake3_native(b"");
        for i in 0..DIGEST_BYTES {
            let got = byte_var_value(&cs, out[i]);
            assert_eq!(got, expected[i], "byte {i} mismatch");
        }
    }

    #[test]
    fn blake3_in_circuit_block_boundaries() {
        // Each of these lengths exercises a boundary in the multi-block /
        // flag bookkeeping:
        // 63 — single sub-block, CHUNK_START | CHUNK_END | ROOT
        // 64 — single block, full block length
        // 65 — two blocks (CHUNK_START + CHUNK_END | ROOT)
        // 127 — two blocks, second is partial
        // 128 — exactly two full blocks
        // 1023 — sixteen blocks, last partial (single chunk boundary)
        // 1024 — sixteen full blocks (single chunk boundary, exact)
        let lens = [63usize, 64, 65, 127, 128, 1023, 1024];
        let mut rng = StdRng::seed_from_u64(0x0B3B_0DE5);
        for &len in &lens {
            let input: Vec<u8> = (0..len).map(|_| rng.r#gen()).collect();

            let cs = ConstraintSystem::<Fr>::new_ref();
            let map = WitnessMap::<Fr>::new();
            let mut b = R1csBuilder::new(cs.clone(), Some(&map));
            b.finish_public_pass();

            let in_vars: Vec<(Variable, Option<Fr>)> =
                input.iter().map(|&byte| alloc_byte(&mut b, byte)).collect();

            let out = blake3_in_circuit(&mut b, &in_vars).unwrap();
            assert!(
                cs.is_satisfied().unwrap(),
                "constraint system unsatisfied at len={len}"
            );

            let expected = blake3_native(&input);
            for i in 0..DIGEST_BYTES {
                let got = byte_var_value(&cs, out[i]);
                assert_eq!(got, expected[i], "byte {i} mismatch at len={len}");
            }
        }
    }

    #[test]
    fn blake3_in_circuit_random_lengths() {
        let mut rng = StdRng::seed_from_u64(0xB3_DA_7A_55);
        // Random non-trivial lengths up to the single-chunk limit.
        let lens = [3usize, 31, 200, 511, 800];
        for &len in &lens {
            let input: Vec<u8> = (0..len).map(|_| rng.r#gen()).collect();
            let cs = ConstraintSystem::<Fr>::new_ref();
            let map = WitnessMap::<Fr>::new();
            let mut b = R1csBuilder::new(cs.clone(), Some(&map));
            b.finish_public_pass();

            let in_vars: Vec<(Variable, Option<Fr>)> =
                input.iter().map(|&byte| alloc_byte(&mut b, byte)).collect();

            let out = blake3_in_circuit(&mut b, &in_vars).unwrap();
            assert!(
                cs.is_satisfied().unwrap(),
                "constraint system unsatisfied at len={len}"
            );

            let expected = blake3_native(&input);
            for i in 0..DIGEST_BYTES {
                let got = byte_var_value(&cs, out[i]);
                assert_eq!(got, expected[i], "byte {i} mismatch at len={len}");
            }
        }
    }

    #[test]
    fn blake3_in_circuit_matches_native_multi_chunk_boundaries() {
        // Exercise inputs that cross the 1024-byte single-chunk boundary and
        // some additional multi-chunk shapes (3-chunk balanced/unbalanced
        // trees, partial-tail chunks).
        let mut rng = StdRng::seed_from_u64(0xB3_5B_25_99);
        // Keep lengths modest to bound test time — each ec_add equivalent in
        // Blake3 is much cheaper than ECDSA, but the constraint count still
        // grows linearly with input size.
        for &len in &[1025usize, 1500, 2048, 2049, 3000] {
            let cs = ConstraintSystem::<Fr>::new_ref();
            let map = WitnessMap::<Fr>::new();
            let mut b = R1csBuilder::new(cs.clone(), Some(&map));
            b.finish_public_pass();

            let input: Vec<u8> = (0..len).map(|_| rng.r#gen()).collect();
            let in_vars: Vec<(Variable, Option<Fr>)> =
                input.iter().map(|&byte| alloc_byte(&mut b, byte)).collect();
            let out = blake3_in_circuit(&mut b, &in_vars).unwrap();
            assert!(cs.is_satisfied().unwrap(), "CS unsatisfied at len={len}");
            let expected = blake3_native(&input);
            for i in 0..32 {
                let got = byte_var_value(&cs, out[i]);
                assert_eq!(got, expected[i], "byte {i} mismatch at len={len}");
            }
        }
    }
}
