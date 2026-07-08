//! `xark-sha256`: a SHA-256 single-block compression-function gadget written
//! entirely in the `xark` `Field` subset.
//!
//! Circuit authors just `use xark_sha256::sha256_block;` — the compiler inlines
//! the whole compression (message schedule + all 64 rounds are `while`-loop
//! unrolled at compile time), so it lowers to the same R1CS as if written
//! inline. It builds on the VERIFIED 32-bit word layer in `xark-bits`.
//!
//! ## Conventions
//!
//! - A 32-bit word is a `[Field; 32]` of little-endian bits (bit `i` has weight
//!   `2^i`), matching `xark-bits`.
//! - Every bitwise op (`ch`, `maj`, the `Σ`/`σ` functions) operates bit-by-bit
//!   on those `[Field; 32]` words.
//! - Rotations/shifts (`rotr32`, `shr32`) are pure re-wiring: ZERO gates.
//!
//! ## Cost model (only `var * var` products emit an R1CS gate)
//!
//! - `+`, `-`, `constant * var` fold into linear combinations: FREE.
//! - `xor32`/`and32` = 32 gates each; `not32`/`rotr32`/`shr32` = 0 gates.
//! - `to_bits32` = 32 booleanity gates; `reduce40` = 40 booleanity gates.
//! - Adding round constants `K[t]` costs NOTHING — they enter as a field
//!   constant in a `reduce40` sum, so no bit array is materialised for them.
//!
//! ## Multi-add strategy
//!
//! SHA-256 mixes several 32-bit words with modular (`mod 2^32`) addition.
//! Rather than chaining `xark_bits::add32` (33 gates apiece), we sum the terms
//! as *field* elements — free — and decompose the total ONCE with `reduce40`
//! (40 gates). Up to ~6 added 32-bit words / constants fit under `2^40`, which
//! covers every SHA-256 addition (max is the 5-term `T1`).

#![no_std]
// Circuit-lowered gadget code: the xark compiler rejects compound assignment on
// `Field` (`+=`/`-=`/`*=`), so `x = x + y` is required — not a clippy oversight.
#![allow(clippy::assign_op_pattern)]

use xark::{assert_eq, Field};
use xark_bits::{and32, not32, rotr32, shr32, xor32};

// ===========================================================================
// Modular reduction: reduce a field sum (< 2^40) to its low 32 bits (mod 2^32).
// ===========================================================================

/// Reduce a field `sum` (assumed `< 2^40`, i.e. up to ~6 added 32-bit words /
/// constants) modulo `2^32`, returning the low 32 bits as a word.
///
/// The prover supplies 40 non-deterministic advice bits; we constrain each to
/// be boolean and constrain their weighted recomposition to equal `sum`. That
/// pins the bits to the true 40-bit binary expansion of `sum`, so returning
/// `bits[0..32]` yields exactly `sum mod 2^32` (the high 8 bits are the carry,
/// discarded).
///
/// Cost: 40 booleanity gates + 1 recomposition equality (0 gates).
fn reduce40(sum: Field) -> [Field; 32] {
    // 40 DISTINCT advice bits (a `while` loop, not `[Field::advice(); 40]`
    // which would repeat one variable).
    let mut bits = [Field::from(0u8); 40];
    let mut i = 0usize;
    while i < 40usize {
        bits[i] = Field::hint_bit(sum, i); // witness-gen: bits[i] = bit(sum, i)
        i += 1;
    }

    // Booleanity: every advice bit is 0 or 1.
    let mut i = 0usize;
    while i < 40usize {
        bits[i].assert_bool();
        i += 1;
    }

    // Recomposition: acc = Σ bits[i] * 2^i, then constrain acc == sum. Each
    // `bits[i] * pow` is variable × constant (no gate); the doubling `pow`
    // stays a compile-time constant.
    let mut acc = Field::from(0u8);
    let mut pow = Field::from(1u8);
    let mut i = 0usize;
    while i < 40usize {
        acc = acc + bits[i] * pow;
        pow = pow + pow;
        i += 1;
    }
    assert_eq(acc, sum);

    // Low 32 bits = the reduced word.
    let mut out = [Field::from(0u8); 32];
    let mut i = 0usize;
    while i < 32usize {
        out[i] = bits[i];
        i += 1;
    }
    out
}

// ===========================================================================
// SHA-256 round functions (all on 32-bit `[Field; 32]` words).
//
// FIPS 180-4 §4.1.2:
//   Ch(e,f,g)  = (e AND f) XOR ((NOT e) AND g)
//   Maj(a,b,c) = (a AND b) XOR (a AND c) XOR (b AND c)
//   Σ0(a) = ROTR2(a)  XOR ROTR13(a) XOR ROTR22(a)
//   Σ1(e) = ROTR6(e)  XOR ROTR11(e) XOR ROTR25(e)
//   σ0(x) = ROTR7(x)  XOR ROTR18(x) XOR SHR3(x)
//   σ1(x) = ROTR17(x) XOR ROTR19(x) XOR SHR10(x)
// ===========================================================================

/// Copy a 32-bit word into a fresh whole local.
///
/// Extract one 32-bit word from a nested `[[Field; 32]; 64]` at index `t` into a
/// fresh flat local (zero gates).
///
/// This exists to work within the circuit subset's storage model: reading a
/// whole inner `[Field; 32]` *out of* a nested array (`arr[t]` as a value) is
/// NOT supported — rustc lowers it to a whole-inner-array copy that the compiler
/// drops. Only *scalar* nested access (`arr[t][j]`) is supported, so we rebuild
/// the word element-by-element here.
fn read64(arr: [[Field; 32]; 64], t: usize) -> [Field; 32] {
    let mut out = [Field::from(0u8); 32];
    let mut j = 0usize;
    while j < 32usize {
        out[j] = arr[t][j];
        j += 1;
    }
    out
}

/// Extract one 32-bit word from a nested `[[Field; 32]; 8]` at index `t` into a
/// fresh flat local (zero gates). See [`read64`] for why this is needed.
fn read8(arr: [[Field; 32]; 8], t: usize) -> [Field; 32] {
    let mut out = [Field::from(0u8); 32];
    let mut j = 0usize;
    while j < 32usize {
        out[j] = arr[t][j];
        j += 1;
    }
    out
}

/// `Ch(e,f,g) = (e AND f) XOR ((NOT e) AND g)`. Cost: 2 AND + 1 XOR = 96 gates.
fn ch(e: [Field; 32], f: [Field; 32], g: [Field; 32]) -> [Field; 32] {
    xor32(and32(e, f), and32(not32(e), g))
}

/// `Maj(a,b,c) = (a AND b) XOR (a AND c) XOR (b AND c)`. Cost: 3 AND + 2 XOR = 160 gates.
fn maj(a: [Field; 32], b: [Field; 32], c: [Field; 32]) -> [Field; 32] {
    xor32(xor32(and32(a, b), and32(a, c)), and32(b, c))
}

/// `Σ0(a) = ROTR2(a) XOR ROTR13(a) XOR ROTR22(a)`. Cost: 2 XOR = 64 gates (rotations free).
fn big_sigma0(a: [Field; 32]) -> [Field; 32] {
    xor32(xor32(rotr32(a, 2), rotr32(a, 13)), rotr32(a, 22))
}

/// `Σ1(e) = ROTR6(e) XOR ROTR11(e) XOR ROTR25(e)`. Cost: 2 XOR = 64 gates.
fn big_sigma1(e: [Field; 32]) -> [Field; 32] {
    xor32(xor32(rotr32(e, 6), rotr32(e, 11)), rotr32(e, 25))
}

/// `σ0(x) = ROTR7(x) XOR ROTR18(x) XOR SHR3(x)`. Cost: 2 XOR = 64 gates.
fn small_sigma0(x: [Field; 32]) -> [Field; 32] {
    xor32(xor32(rotr32(x, 7), rotr32(x, 18)), shr32(x, 3))
}

/// `σ1(x) = ROTR17(x) XOR ROTR19(x) XOR SHR10(x)`. Cost: 2 XOR = 64 gates.
fn small_sigma1(x: [Field; 32]) -> [Field; 32] {
    xor32(xor32(rotr32(x, 17), rotr32(x, 19)), shr32(x, 10))
}

// ===========================================================================
// Compression function (FIPS 180-4 §6.2.2).
// ===========================================================================

/// SHA-256 single-block compression.
///
/// - `h_in`: the 8 incoming hash words `a..h` (each a `[Field; 32]` word).
/// - `w`:    the 16 message-schedule words `W[0..16]` for this block.
///
/// Returns the 8 updated hash words. All additions are `mod 2^32` via
/// `reduce40`. The 64-round loop and the 48-step schedule extension are fully
/// unrolled at compile time.
fn compress(h_in: [[Field; 32]; 8], w: [[Field; 32]; 16]) -> [[Field; 32]; 8] {
    // --- Round-constant table K[0..64] (FIPS 180-4 §4.2.2), as field
    // constants. Adding K[t] into a `reduce40` sum is free (no bit array). ---
    let k: [Field; 64] = [
        Field::from(1116352408u32), // K[0]  = 0x428a2f98
        Field::from(1899447441u32), // K[1]  = 0x71374491
        Field::from(3049323471u32), // K[2]  = 0xb5c0fbcf
        Field::from(3921009573u32), // K[3]  = 0xe9b5dba5
        Field::from(961987163u32),  // K[4]  = 0x3956c25b
        Field::from(1508970993u32), // K[5]  = 0x59f111f1
        Field::from(2453635748u32), // K[6]  = 0x923f82a4
        Field::from(2870763221u32), // K[7]  = 0xab1c5ed5
        Field::from(3624381080u32), // K[8]  = 0xd807aa98
        Field::from(310598401u32),  // K[9]  = 0x12835b01
        Field::from(607225278u32),  // K[10] = 0x243185be
        Field::from(1426881987u32), // K[11] = 0x550c7dc3
        Field::from(1925078388u32), // K[12] = 0x72be5d74
        Field::from(2162078206u32), // K[13] = 0x80deb1fe
        Field::from(2614888103u32), // K[14] = 0x9bdc06a7
        Field::from(3248222580u32), // K[15] = 0xc19bf174
        Field::from(3835390401u32), // K[16] = 0xe49b69c1
        Field::from(4022224774u32), // K[17] = 0xefbe4786
        Field::from(264347078u32),  // K[18] = 0x0fc19dc6
        Field::from(604807628u32),  // K[19] = 0x240ca1cc
        Field::from(770255983u32),  // K[20] = 0x2de92c6f
        Field::from(1249150122u32), // K[21] = 0x4a7484aa
        Field::from(1555081692u32), // K[22] = 0x5cb0a9dc
        Field::from(1996064986u32), // K[23] = 0x76f988da
        Field::from(2554220882u32), // K[24] = 0x983e5152
        Field::from(2821834349u32), // K[25] = 0xa831c66d
        Field::from(2952996808u32), // K[26] = 0xb00327c8
        Field::from(3210313671u32), // K[27] = 0xbf597fc7
        Field::from(3336571891u32), // K[28] = 0xc6e00bf3
        Field::from(3584528711u32), // K[29] = 0xd5a79147
        Field::from(113926993u32),  // K[30] = 0x06ca6351
        Field::from(338241895u32),  // K[31] = 0x14292967
        Field::from(666307205u32),  // K[32] = 0x27b70a85
        Field::from(773529912u32),  // K[33] = 0x2e1b2138
        Field::from(1294757372u32), // K[34] = 0x4d2c6dfc
        Field::from(1396182291u32), // K[35] = 0x53380d13
        Field::from(1695183700u32), // K[36] = 0x650a7354
        Field::from(1986661051u32), // K[37] = 0x766a0abb
        Field::from(2177026350u32), // K[38] = 0x81c2c92e
        Field::from(2456956037u32), // K[39] = 0x92722c85
        Field::from(2730485921u32), // K[40] = 0xa2bfe8a1
        Field::from(2820302411u32), // K[41] = 0xa81a664b
        Field::from(3259730800u32), // K[42] = 0xc24b8b70
        Field::from(3345764771u32), // K[43] = 0xc76c51a3
        Field::from(3516065817u32), // K[44] = 0xd192e819
        Field::from(3600352804u32), // K[45] = 0xd6990624
        Field::from(4094571909u32), // K[46] = 0xf40e3585
        Field::from(275423344u32),  // K[47] = 0x106aa070
        Field::from(430227734u32),  // K[48] = 0x19a4c116
        Field::from(506948616u32),  // K[49] = 0x1e376c08
        Field::from(659060556u32),  // K[50] = 0x2748774c
        Field::from(883997877u32),  // K[51] = 0x34b0bcb5
        Field::from(958139571u32),  // K[52] = 0x391c0cb3
        Field::from(1322822218u32), // K[53] = 0x4ed8aa4a
        Field::from(1537002063u32), // K[54] = 0x5b9cca4f
        Field::from(1747873779u32), // K[55] = 0x682e6ff3
        Field::from(1955562222u32), // K[56] = 0x748f82ee
        Field::from(2024104815u32), // K[57] = 0x78a5636f
        Field::from(2227730452u32), // K[58] = 0x84c87814
        Field::from(2361852424u32), // K[59] = 0x8cc70208
        Field::from(2428436474u32), // K[60] = 0x90befffa
        Field::from(2756734187u32), // K[61] = 0xa4506ceb
        Field::from(3204031479u32), // K[62] = 0xbef9a3f7
        Field::from(3329325298u32), // K[63] = 0xc67178f2
    ];

    // A constant-zero word, used to size/initialise the arrays below.
    let zero = [Field::from(0u8); 32];

    // --- 1. Message schedule: W[0..16] = input; extend to W[16..64]. ---
    //   W[t] = σ1(W[t-2]) + W[t-7] + σ0(W[t-15]) + W[t-16]   (mod 2^32)
    //
    // Words are written into the nested `sched` array bit-by-bit (scalar slot
    // writes), the only nested-array store the subset supports.
    let mut sched = [zero; 64];
    let mut t = 0usize;
    while t < 16usize {
        let mut j = 0usize;
        while j < 32usize {
            sched[t][j] = w[t][j];
            j += 1;
        }
        t += 1;
    }
    let mut t = 16usize;
    while t < 64usize {
        // Pull the four source words into flat locals (whole inner-array reads
        // from `sched` aren't supported, so extract each via `read64`).
        let wm2 = read64(sched, t - 2);
        let wm7 = read64(sched, t - 7);
        let wm15 = read64(sched, t - 15);
        let wm16 = read64(sched, t - 16);
        let s1 = small_sigma1(wm2);
        let s0 = small_sigma0(wm15);
        // Four 32-bit words -> sum < 2^34, safely within reduce40's 2^40 range.
        let sum = Field::from_bits::<32>(s1)
            + Field::from_bits::<32>(wm7)
            + Field::from_bits::<32>(s0)
            + Field::from_bits::<32>(wm16);
        let word = reduce40(sum);
        let mut j = 0usize;
        while j < 32usize {
            sched[t][j] = word[j];
            j += 1;
        }
        t += 1;
    }

    // --- 2. Initialise working variables a..h from the incoming hash. ---
    // Keep the incoming words as flat locals too — they are reused in step 4.
    let hi0 = read8(h_in, 0);
    let hi1 = read8(h_in, 1);
    let hi2 = read8(h_in, 2);
    let hi3 = read8(h_in, 3);
    let hi4 = read8(h_in, 4);
    let hi5 = read8(h_in, 5);
    let hi6 = read8(h_in, 6);
    let hi7 = read8(h_in, 7);
    let mut a = hi0; // whole flat-local copies (supported)
    let mut b = hi1;
    let mut c = hi2;
    let mut d = hi3;
    let mut e = hi4;
    let mut f = hi5;
    let mut g = hi6;
    let mut h = hi7;

    // --- 3. 64 compression rounds. ---
    // T1 and T2 are only ever consumed by further field additions (into `e` and
    // `a`), never by bitwise ops, so they need NOT be reduced to 32-bit words
    // here. We keep them as raw field sums and reduce ONCE when forming `e` and
    // `a`. This is exact SHA-256 (the mod 2^32 lands at `e`/`a`) but emits two
    // fewer `reduce40` decompositions per round (more compact R1CS).
    let mut t = 0usize;
    while t < 64usize {
        let wt = read64(sched, t); // W[t] as a flat local
                                   // T1 = h + Σ1(e) + Ch(e,f,g) + K[t] + W[t]  (raw field sum, < 2^35)
        let bsig1 = big_sigma1(e);
        let chv = ch(e, f, g);
        let t1 = Field::from_bits::<32>(h)
            + Field::from_bits::<32>(bsig1)
            + Field::from_bits::<32>(chv)
            + k[t]
            + Field::from_bits::<32>(wt);

        // T2 = Σ0(a) + Maj(a,b,c)  (raw field sum, < 2^33)
        let bsig0 = big_sigma0(a);
        let majv = maj(a, b, c);
        let t2 = Field::from_bits::<32>(bsig0) + Field::from_bits::<32>(majv);

        // Shift the working variables. Order matters: `e` uses the CURRENT `d`,
        // so update `e` before `d = c`.
        h = g;
        g = f;
        f = e;
        // e = (d + T1) mod 2^32   (d < 2^32, T1 < 2^35 -> sum < 2^36 < 2^40)
        e = reduce40(Field::from_bits::<32>(d) + t1);
        d = c;
        c = b;
        b = a;
        // a = (T1 + T2) mod 2^32   (< 2^35 + 2^33 < 2^36 < 2^40)
        a = reduce40(t1 + t2);

        t += 1;
    }

    // --- 4. Add the compressed chunk to the incoming hash (mod 2^32). ---
    // out[i] = (h_in[i] + working_i) mod 2^32, written bit-by-bit into `out`.
    let mut out = [zero; 8];
    let o0 = reduce40(Field::from_bits::<32>(hi0) + Field::from_bits::<32>(a));
    let o1 = reduce40(Field::from_bits::<32>(hi1) + Field::from_bits::<32>(b));
    let o2 = reduce40(Field::from_bits::<32>(hi2) + Field::from_bits::<32>(c));
    let o3 = reduce40(Field::from_bits::<32>(hi3) + Field::from_bits::<32>(d));
    let o4 = reduce40(Field::from_bits::<32>(hi4) + Field::from_bits::<32>(e));
    let o5 = reduce40(Field::from_bits::<32>(hi5) + Field::from_bits::<32>(f));
    let o6 = reduce40(Field::from_bits::<32>(hi6) + Field::from_bits::<32>(g));
    let o7 = reduce40(Field::from_bits::<32>(hi7) + Field::from_bits::<32>(h));
    let mut j = 0usize;
    while j < 32usize {
        out[0][j] = o0[j];
        out[1][j] = o1[j];
        out[2][j] = o2[j];
        out[3][j] = o3[j];
        out[4][j] = o4[j];
        out[5][j] = o5[j];
        out[6][j] = o6[j];
        out[7][j] = o7[j];
        j += 1;
    }
    out
}

// ===========================================================================
// Convenience wrapper: compress a single 16-word block from the standard IV.
// ===========================================================================

/// The SHA-256 initial hash value H0 (FIPS 180-4 §5.3.3), as field constants.
fn h0() -> [Field; 8] {
    [
        Field::from(1779033703u32), // 0x6a09e667
        Field::from(3144134277u32), // 0xbb67ae85
        Field::from(1013904242u32), // 0x3c6ef372
        Field::from(2773480762u32), // 0xa54ff53a
        Field::from(1359893119u32), // 0x510e527f
        Field::from(2600822924u32), // 0x9b05688c
        Field::from(528734635u32),  // 0x1f83d9ab
        Field::from(1541459225u32), // 0x5be0cd19
    ]
}

/// Compress one 16-word message block starting from the standard IV `H0`,
/// returning the 8 output hash words (each a `[Field; 32]` little-endian word).
///
/// `w` holds the 16 message words already decomposed to bits (e.g. via
/// `xark_bits::to_bits32`). This is a single-block compression: it performs no
/// padding and no multi-block chaining — the caller is responsible for the
/// message layout.
pub fn sha256_block(w: [[Field; 32]; 16]) -> [[Field; 32]; 8] {
    // Decompose the constant IV words into boolean-constrained bit arrays so
    // they can feed the bitwise round functions.
    let hc = h0();
    let zero = [Field::from(0u8); 32];
    let mut h_in = [zero; 8];
    let mut i = 0usize;
    while i < 8usize {
        let word = hc[i].to_bits::<32>();
        let mut j = 0usize;
        while j < 32usize {
            h_in[i][j] = word[j];
            j += 1;
        }
        i += 1;
    }
    compress(h_in, w)
}

// ===========================================================================
// Variable-length SHA-256 via Merkle–Damgård chaining over `compress`.
// ===========================================================================

/// Variable-length SHA-256. `N_BYTES` is a compile-time constant (a circuit is
/// fixed-size), so the padding geometry and the block loop resolve/unroll at
/// compile time.
///
/// `msg` is the message as raw bytes, one `Field` per byte (each is
/// range-checked to `0..=255` by decomposing it with `to_bits::<8>()`, which
/// also yields the bits we pack into the message words). The digest is returned
/// as 8 output words (each a `[Field; 32]` little-endian-bit word), i.e. the
/// 256-bit hash.
///
/// ## Construction (FIPS 180-4)
///
/// - Start from the initial hash value `H0` (`h0()`), decomposed to bits.
/// - Pad the message: append one `0x80` byte, then the minimum number of zero
///   bytes, then the 64-bit **big-endian** message *bit* length, so the total
///   is a multiple of 64 bytes. `N_BYTES` is `const`, so the padded length
///   `total_len` and block count `n_blocks` are compile-time constants.
/// - Split into 64-byte blocks; each block is sixteen 32-bit **big-endian**
///   words (`w[0]` = bytes `0..4`, the first byte is the most-significant),
///   matching `sha256_block`'s `w` layout.
/// - Chain: `h = compress(h, block)` for every block (the last output words are
///   copied back into `h` scalar-by-scalar, the only nested-array store the
///   subset supports — see `sha256_block` / `read8`).
///
/// Since it reuses the verified `compress`, every block costs exactly one
/// `sha256_block`-worth of compression gates plus the byte range-checks.
pub fn sha256<const N_BYTES: usize>(msg: [Field; N_BYTES]) -> [[Field; 32]; 8] {
    let zero = [Field::from(0u8); 32];

    // --- Compile-time padded geometry ---
    // Message bit-length (goes into the last 8 bytes, big-endian).
    let bit_length = (N_BYTES as u64) * 8u64;
    // Padded length = smallest multiple of 64 that fits the message plus the
    // 0x80 delimiter (1 byte) and the 64-bit length field (8 bytes):
    //   n_blocks = ceil((N_BYTES + 9) / 64) = (N_BYTES + 9 + 63) / 64.
    let n_blocks = (N_BYTES + 72usize) / 64usize;
    let total_len = n_blocks * 64usize;

    // --- h = IV (H0) decomposed to bits ---
    let hc = h0();
    let mut h = [zero; 8];
    let mut i = 0usize;
    while i < 8usize {
        let word = hc[i].to_bits::<32>();
        let mut j = 0usize;
        while j < 32usize {
            h[i][j] = word[j];
            j += 1;
        }
        i += 1;
    }

    // --- Process one 64-byte block at a time (loop bound is compile-time). ---
    let mut b = 0usize;
    while b < n_blocks {
        // Assemble this block's 16 big-endian 32-bit words. Word `t` covers
        // bytes `4t..4t+4`; byte `k` (k=0 is the most-significant) occupies word
        // bits `(3-k)*8 .. (3-k)*8+8`.
        let mut w = [zero; 16];
        let mut t = 0usize;
        while t < 16usize {
            let mut k = 0usize;
            while k < 4usize {
                let pos = b * 64usize + t * 4usize + k;
                // Decide this padded byte's value. `pos`, `N_BYTES` and
                // `total_len` are all compile-time constants inside the unrolled
                // loops, so every branch is resolved at compile time (same
                // pattern as the Poseidon2 sponge's `if i+1 < N`).
                let byte = if pos < N_BYTES {
                    // Real message byte (a witness variable).
                    msg[pos]
                } else if pos == N_BYTES {
                    // The single `0x80` padding delimiter.
                    Field::from(128u32)
                } else if pos + 8usize >= total_len {
                    // One of the 8 big-endian length bytes; `m = 0` is the MSB.
                    let m = pos + 8usize - total_len;
                    // divisor = 256^(7 - m), built with `*` only (no shifts).
                    let mut divisor = 1u64;
                    let mut p = 0usize;
                    while p < 7usize - m {
                        divisor = divisor * 256u64;
                        p += 1;
                    }
                    Field::from((bit_length / divisor) % 256u64)
                } else {
                    // Interior zero padding.
                    Field::from(0u8)
                };

                // Range-check (0..=255) AND decompose in one step, then place the
                // 8 little-endian byte bits big-endian within the word.
                let bits = byte.to_bits::<8>();
                let off = (3usize - k) * 8usize;
                let mut j = 0usize;
                while j < 8usize {
                    w[t][off + j] = bits[j];
                    j += 1;
                }
                k += 1;
            }
            t += 1;
        }

        // Chain: h = compress(h, w). The 8 output words are copied back into `h`
        // scalar-by-scalar (whole nested-array reassignment isn't supported;
        // `read8` pulls each word out of the return value into a flat local).
        let full = compress(h, w);
        let mut i = 0usize;
        while i < 8usize {
            let word = read8(full, i);
            let mut j = 0usize;
            while j < 32usize {
                h[i][j] = word[j];
                j += 1;
            }
            i += 1;
        }

        b += 1;
    }

    h
}
