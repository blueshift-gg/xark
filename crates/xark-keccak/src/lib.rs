//! `xark-keccak`: a Keccak-f[1600] permutation and Keccak-256 (Ethereum-flavour)
//! gadget written entirely in the `xark` `Field` subset.
//!
//! Circuit authors just `use xark_keccak::keccak256_block;` — the compiler
//! inlines everything (all 24 rounds and the θ/ρ/π/χ/ι steps are `while`-loop
//! unrolled at compile time), so it lowers to the same R1CS as if written
//! inline. It builds on the VERIFIED 64-bit word layer in `xark-bits`.
//!
//! ## State & conventions
//!
//! - The 1600-bit state is 25 lanes of 64 bits: `[[Field; 64]; 25]`.
//! - Lanes are indexed `x + 5*y` with `x, y ∈ 0..5` (`x` = column, `y` = row),
//!   the standard Keccak convention.
//! - Each lane is a `[Field; 64]` of little-endian bits (bit `i` has weight
//!   `2^i`), matching `xark-bits`. Lane byte-order is little-endian.
//!
//! ## Cost model (only `var * var` products emit an R1CS gate)
//!
//! - `xor64`/`and64` = 64 gates each; `not64`/`rotl64` (ρ rotations) = 0 gates.
//! - θ is all XORs and one rotate: cheap. ρ/π are pure lane re-wiring: FREE.
//! - χ is the only source of AND gates — it dominates the gate count.
//! - ι XORs lane 0 with a round constant that is a *compile-time constant* bit
//!   lane, so each `bit.xor(const)` folds to `bit + const - 2*bit*const`
//!   where `bit*const` is variable × constant: FREE (0 gates).
//! - `to_bits64` on each input word (in the demo) costs 64 booleanity gates.
//!
//! Per round: θ ≈ 50 `xor64`, χ = 25 `and64` + 25 `xor64` → ~100 word-ops ×
//! 64 bits ≈ 6400 gates, × 24 rounds ≈ 154k gates for the permutation.

#![no_std]

use xark::Field;
use xark_bits::{and64, not64, rotl64, xor64};

// ===========================================================================
// Lane readers. Reading a whole inner `[Field; 64]` *out of* a nested array
// (`s[i]` as a value) is NOT supported by the circuit subset — rustc lowers it
// to a whole-inner-array copy that the compiler drops. Only *scalar* nested
// access (`s[i][j]`) works, so we rebuild the lane element-by-element (0 gates).
// ===========================================================================

/// Read lane `i` out of a 25-lane state into a fresh flat `[Field; 64]`.
fn read25(s: [[Field; 64]; 25], i: usize) -> [Field; 64] {
    let mut out = [Field::from(0u8); 64];
    let mut j = 0usize;
    while j < 64usize {
        out[j] = s[i][j];
        j += 1;
    }
    out
}

/// Read lane `i` out of a 5-lane array (the θ column parities `C`).
fn read5(s: [[Field; 64]; 5], i: usize) -> [Field; 64] {
    let mut out = [Field::from(0u8); 64];
    let mut j = 0usize;
    while j < 64usize {
        out[j] = s[i][j];
        j += 1;
    }
    out
}

/// Read lane `r` out of the 24-row round-constant bit table.
fn read24(s: [[Field; 64]; 24], r: usize) -> [Field; 64] {
    let mut out = [Field::from(0u8); 64];
    let mut j = 0usize;
    while j < 64usize {
        out[j] = s[r][j];
        j += 1;
    }
    out
}

// ===========================================================================
// The five Keccak-f step mappings. Each takes the 25-lane state and returns the
// updated 25-lane state (whole nested-array params/returns are supported, as in
// the SHA-256 gadget).
// ===========================================================================

/// θ (theta): `C[x] = ⊕_y A[x,y]`, `D[x] = C[x-1] ⊕ rotl(C[x+1], 1)`, then
/// `A[x,y] ⊕= D[x]`. All XOR + one rotate. Cost: 20 (C) + 5 (D) + 25 (apply) =
/// 50 `xor64` per call.
fn theta(a: [[Field; 64]; 25]) -> [[Field; 64]; 25] {
    let zero = [Field::from(0u8); 64];

    // Column parities C[x] = A[x,0] ⊕ A[x,1] ⊕ A[x,2] ⊕ A[x,3] ⊕ A[x,4].
    let mut c = [zero; 5];
    let mut x = 0usize;
    while x < 5usize {
        let mut lane = read25(a, x);
        lane = xor64(lane, read25(a, x + 5));
        lane = xor64(lane, read25(a, x + 10));
        lane = xor64(lane, read25(a, x + 15));
        lane = xor64(lane, read25(a, x + 20));
        let mut j = 0usize;
        while j < 64usize {
            c[x][j] = lane[j];
            j += 1;
        }
        x += 1;
    }

    // D[x] = C[x-1] ⊕ rotl(C[x+1], 1); apply A[x,y] ⊕= D[x] into a fresh state.
    let mut out = [zero; 25];
    let mut x = 0usize;
    while x < 5usize {
        let cm1 = read5(c, (x + 4) % 5); // C[x-1]
        let cp1 = read5(c, (x + 1) % 5); // C[x+1]
        let d = xor64(cm1, rotl64(cp1, 1));
        let mut y = 0usize;
        while y < 5usize {
            let lane = read25(a, x + 5 * y);
            let nl = xor64(lane, d);
            let mut j = 0usize;
            while j < 64usize {
                out[x + 5 * y][j] = nl[j];
                j += 1;
            }
            y += 1;
        }
        x += 1;
    }
    out
}

/// ρ (rho) + π (pi) fused and fully unrolled. Each lane is rotated left by its
/// fixed offset (ρ) and moved to B[y, 2x+3y] (π). The rotation offsets must be
/// literals here: the compiler only tracks literals / loop-counter arithmetic as
/// compile-time constants, not values read from a table, and `rotl64` indexes by
/// its offset. Pure re-wiring: 0 gates.
fn rho_pi(a: [[Field; 64]; 25]) -> [[Field; 64]; 25] {
    let zero = [Field::from(0u8); 64];
    let mut b = [zero; 25];
    // A[x=0,y=0] (lane 0) rotl 0 -> B lane 0
    let l0 = rotl64(read25(a, 0), 0);
    let mut j0 = 0usize;
    while j0 < 64usize {
        b[0][j0] = l0[j0];
        j0 += 1;
    }
    // A[x=1,y=0] (lane 1) rotl 1 -> B lane 10
    let l1 = rotl64(read25(a, 1), 1);
    let mut j1 = 0usize;
    while j1 < 64usize {
        b[10][j1] = l1[j1];
        j1 += 1;
    }
    // A[x=2,y=0] (lane 2) rotl 62 -> B lane 20
    let l2 = rotl64(read25(a, 2), 62);
    let mut j2 = 0usize;
    while j2 < 64usize {
        b[20][j2] = l2[j2];
        j2 += 1;
    }
    // A[x=3,y=0] (lane 3) rotl 28 -> B lane 5
    let l3 = rotl64(read25(a, 3), 28);
    let mut j3 = 0usize;
    while j3 < 64usize {
        b[5][j3] = l3[j3];
        j3 += 1;
    }
    // A[x=4,y=0] (lane 4) rotl 27 -> B lane 15
    let l4 = rotl64(read25(a, 4), 27);
    let mut j4 = 0usize;
    while j4 < 64usize {
        b[15][j4] = l4[j4];
        j4 += 1;
    }
    // A[x=0,y=1] (lane 5) rotl 36 -> B lane 16
    let l5 = rotl64(read25(a, 5), 36);
    let mut j5 = 0usize;
    while j5 < 64usize {
        b[16][j5] = l5[j5];
        j5 += 1;
    }
    // A[x=1,y=1] (lane 6) rotl 44 -> B lane 1
    let l6 = rotl64(read25(a, 6), 44);
    let mut j6 = 0usize;
    while j6 < 64usize {
        b[1][j6] = l6[j6];
        j6 += 1;
    }
    // A[x=2,y=1] (lane 7) rotl 6 -> B lane 11
    let l7 = rotl64(read25(a, 7), 6);
    let mut j7 = 0usize;
    while j7 < 64usize {
        b[11][j7] = l7[j7];
        j7 += 1;
    }
    // A[x=3,y=1] (lane 8) rotl 55 -> B lane 21
    let l8 = rotl64(read25(a, 8), 55);
    let mut j8 = 0usize;
    while j8 < 64usize {
        b[21][j8] = l8[j8];
        j8 += 1;
    }
    // A[x=4,y=1] (lane 9) rotl 20 -> B lane 6
    let l9 = rotl64(read25(a, 9), 20);
    let mut j9 = 0usize;
    while j9 < 64usize {
        b[6][j9] = l9[j9];
        j9 += 1;
    }
    // A[x=0,y=2] (lane 10) rotl 3 -> B lane 7
    let l10 = rotl64(read25(a, 10), 3);
    let mut j10 = 0usize;
    while j10 < 64usize {
        b[7][j10] = l10[j10];
        j10 += 1;
    }
    // A[x=1,y=2] (lane 11) rotl 10 -> B lane 17
    let l11 = rotl64(read25(a, 11), 10);
    let mut j11 = 0usize;
    while j11 < 64usize {
        b[17][j11] = l11[j11];
        j11 += 1;
    }
    // A[x=2,y=2] (lane 12) rotl 43 -> B lane 2
    let l12 = rotl64(read25(a, 12), 43);
    let mut j12 = 0usize;
    while j12 < 64usize {
        b[2][j12] = l12[j12];
        j12 += 1;
    }
    // A[x=3,y=2] (lane 13) rotl 25 -> B lane 12
    let l13 = rotl64(read25(a, 13), 25);
    let mut j13 = 0usize;
    while j13 < 64usize {
        b[12][j13] = l13[j13];
        j13 += 1;
    }
    // A[x=4,y=2] (lane 14) rotl 39 -> B lane 22
    let l14 = rotl64(read25(a, 14), 39);
    let mut j14 = 0usize;
    while j14 < 64usize {
        b[22][j14] = l14[j14];
        j14 += 1;
    }
    // A[x=0,y=3] (lane 15) rotl 41 -> B lane 23
    let l15 = rotl64(read25(a, 15), 41);
    let mut j15 = 0usize;
    while j15 < 64usize {
        b[23][j15] = l15[j15];
        j15 += 1;
    }
    // A[x=1,y=3] (lane 16) rotl 45 -> B lane 8
    let l16 = rotl64(read25(a, 16), 45);
    let mut j16 = 0usize;
    while j16 < 64usize {
        b[8][j16] = l16[j16];
        j16 += 1;
    }
    // A[x=2,y=3] (lane 17) rotl 15 -> B lane 18
    let l17 = rotl64(read25(a, 17), 15);
    let mut j17 = 0usize;
    while j17 < 64usize {
        b[18][j17] = l17[j17];
        j17 += 1;
    }
    // A[x=3,y=3] (lane 18) rotl 21 -> B lane 3
    let l18 = rotl64(read25(a, 18), 21);
    let mut j18 = 0usize;
    while j18 < 64usize {
        b[3][j18] = l18[j18];
        j18 += 1;
    }
    // A[x=4,y=3] (lane 19) rotl 8 -> B lane 13
    let l19 = rotl64(read25(a, 19), 8);
    let mut j19 = 0usize;
    while j19 < 64usize {
        b[13][j19] = l19[j19];
        j19 += 1;
    }
    // A[x=0,y=4] (lane 20) rotl 18 -> B lane 14
    let l20 = rotl64(read25(a, 20), 18);
    let mut j20 = 0usize;
    while j20 < 64usize {
        b[14][j20] = l20[j20];
        j20 += 1;
    }
    // A[x=1,y=4] (lane 21) rotl 2 -> B lane 24
    let l21 = rotl64(read25(a, 21), 2);
    let mut j21 = 0usize;
    while j21 < 64usize {
        b[24][j21] = l21[j21];
        j21 += 1;
    }
    // A[x=2,y=4] (lane 22) rotl 61 -> B lane 9
    let l22 = rotl64(read25(a, 22), 61);
    let mut j22 = 0usize;
    while j22 < 64usize {
        b[9][j22] = l22[j22];
        j22 += 1;
    }
    // A[x=3,y=4] (lane 23) rotl 56 -> B lane 19
    let l23 = rotl64(read25(a, 23), 56);
    let mut j23 = 0usize;
    while j23 < 64usize {
        b[19][j23] = l23[j23];
        j23 += 1;
    }
    // A[x=4,y=4] (lane 24) rotl 14 -> B lane 4
    let l24 = rotl64(read25(a, 24), 14);
    let mut j24 = 0usize;
    while j24 < 64usize {
        b[4][j24] = l24[j24];
        j24 += 1;
    }
    b
}

/// χ (chi): `A[x,y] = B[x,y] ⊕ ((¬B[x+1,y]) ∧ B[x+2,y])`. The only AND source.
/// Cost: 25 `and64` + 25 `xor64` per call.
fn chi(b: [[Field; 64]; 25]) -> [[Field; 64]; 25] {
    let zero = [Field::from(0u8); 64];
    let mut out = [zero; 25];
    let mut y = 0usize;
    while y < 5usize {
        let mut x = 0usize;
        while x < 5usize {
            let bx = read25(b, x + 5 * y);
            let bx1 = read25(b, (x + 1) % 5 + 5 * y);
            let bx2 = read25(b, (x + 2) % 5 + 5 * y);
            let t = and64(not64(bx1), bx2);
            let nl = xor64(bx, t);
            let mut j = 0usize;
            while j < 64usize {
                out[x + 5 * y][j] = nl[j];
                j += 1;
            }
            x += 1;
        }
        y += 1;
    }
    out
}

/// The 24 Keccak round constants as compile-time bit lanes (`[[Field; 64]; 24]`,
/// little-endian). XORing lane 0 with one of these (ι) folds to zero gates.
fn rc_bits() -> [[Field; 64]; 24] {
    [
        [
            Field::from(1u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
        ], // RC[0] = 0x0000000000000001
        [
            Field::from(0u8),
            Field::from(1u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(1u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(1u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
        ], // RC[1] = 0x0000000000008082
        [
            Field::from(0u8),
            Field::from(1u8),
            Field::from(0u8),
            Field::from(1u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(1u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(1u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(1u8),
        ], // RC[2] = 0x800000000000808a
        [
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(1u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(1u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(1u8),
        ], // RC[3] = 0x8000000080008000
        [
            Field::from(1u8),
            Field::from(1u8),
            Field::from(0u8),
            Field::from(1u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(1u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(1u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
        ], // RC[4] = 0x000000000000808b
        [
            Field::from(1u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(1u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
        ], // RC[5] = 0x0000000080000001
        [
            Field::from(1u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(1u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(1u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(1u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(1u8),
        ], // RC[6] = 0x8000000080008081
        [
            Field::from(1u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(1u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(1u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(1u8),
        ], // RC[7] = 0x8000000000008009
        [
            Field::from(0u8),
            Field::from(1u8),
            Field::from(0u8),
            Field::from(1u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(1u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
        ], // RC[8] = 0x000000000000008a
        [
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(1u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(1u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
        ], // RC[9] = 0x0000000000000088
        [
            Field::from(1u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(1u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(1u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(1u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
        ], // RC[10] = 0x0000000080008009
        [
            Field::from(0u8),
            Field::from(1u8),
            Field::from(0u8),
            Field::from(1u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(1u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
        ], // RC[11] = 0x000000008000000a
        [
            Field::from(1u8),
            Field::from(1u8),
            Field::from(0u8),
            Field::from(1u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(1u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(1u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(1u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
        ], // RC[12] = 0x000000008000808b
        [
            Field::from(1u8),
            Field::from(1u8),
            Field::from(0u8),
            Field::from(1u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(1u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(1u8),
        ], // RC[13] = 0x800000000000008b
        [
            Field::from(1u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(1u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(1u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(1u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(1u8),
        ], // RC[14] = 0x8000000000008089
        [
            Field::from(1u8),
            Field::from(1u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(1u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(1u8),
        ], // RC[15] = 0x8000000000008003
        [
            Field::from(0u8),
            Field::from(1u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(1u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(1u8),
        ], // RC[16] = 0x8000000000008002
        [
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(1u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(1u8),
        ], // RC[17] = 0x8000000000000080
        [
            Field::from(0u8),
            Field::from(1u8),
            Field::from(0u8),
            Field::from(1u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(1u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
        ], // RC[18] = 0x000000000000800a
        [
            Field::from(0u8),
            Field::from(1u8),
            Field::from(0u8),
            Field::from(1u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(1u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(1u8),
        ], // RC[19] = 0x800000008000000a
        [
            Field::from(1u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(1u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(1u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(1u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(1u8),
        ], // RC[20] = 0x8000000080008081
        [
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(1u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(1u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(1u8),
        ], // RC[21] = 0x8000000000008080
        [
            Field::from(1u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(1u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
        ], // RC[22] = 0x0000000080000001
        [
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(1u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(1u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(1u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(0u8),
            Field::from(1u8),
        ], // RC[23] = 0x8000000080008008
    ]
}

// ===========================================================================
// The permutation and the Keccak-256 single-block hash.
// ===========================================================================

/// Keccak-f[1600]: apply all 24 rounds (θ, ρ, π, χ, ι) to the 25-lane state.
pub fn keccak_f(state: [[Field; 64]; 25]) -> [[Field; 64]; 25] {
    let zero = [Field::from(0u8); 64];

    // Copy the input state into a fresh mutable local, lane-by-lane (scalar
    // writes: the nested-array store the subset supports).
    let mut a = [zero; 25];
    let mut i = 0usize;
    while i < 25usize {
        let mut j = 0usize;
        while j < 64usize {
            a[i][j] = state[i][j];
            j += 1;
        }
        i += 1;
    }

    let rc = rc_bits();

    let mut round = 0usize;
    while round < 24usize {
        a = theta(a);
        a = rho_pi(a);
        a = chi(a);
        // ι: A[0,0] ⊕= RC[round]. `rc_lane[b]` is a compile-time constant, so
        // each `bit_xor` folds to no gate.
        let rc_lane = read24(rc, round);
        let mut b = 0usize;
        while b < 64usize {
            a[0][b] = a[0][b].xor(rc_lane[b]);
            b += 1;
        }
        round += 1;
    }
    a
}

/// Keccak-256 (Ethereum / `keccak256`, NOT NIST SHA3) on a single already-padded
/// rate block.
///
/// `block` holds the 17 rate lanes (`r = 1088` bits) of one message block that
/// the caller has already padded with Ethereum's `pad10*1` using the **0x01**
/// domain byte (NIST SHA3 would use 0x06). Absorption into a zero state makes
/// the 25-lane state `[block[0..17], 0, 0, ..., 0]` (capacity lanes zero), which
/// we permute once and squeeze: the first 256 output bits are lanes 0..4.
///
/// Returns the 4 digest lanes (each a `[Field; 64]` little-endian word).
pub fn keccak256_block(block: [[Field; 64]; 17]) -> [[Field; 64]; 4] {
    let zero = [Field::from(0u8); 64];

    // Absorb: state = 0 ⊕ block for the 17 rate lanes; capacity stays zero.
    let mut state = [zero; 25];
    let mut i = 0usize;
    while i < 17usize {
        let mut j = 0usize;
        while j < 64usize {
            state[i][j] = block[i][j];
            j += 1;
        }
        i += 1;
    }

    let permuted = keccak_f(state);

    // Squeeze the first 256 bits = lanes 0..4.
    let mut out = [zero; 4];
    let mut i = 0usize;
    while i < 4usize {
        let mut j = 0usize;
        while j < 64usize {
            out[i][j] = permuted[i][j];
            j += 1;
        }
        i += 1;
    }
    out
}

/// Variable-length Keccak-256 (Ethereum / `keccak256`, `0x01` domain padding),
/// built as a full sponge on top of the VERIFIED `keccak_f` permutation. This
/// does NOT touch `keccak_f` or `keccak256_block`; it only wraps them.
///
/// `N_BYTES` is a compile-time constant (a circuit is fixed-size), so the absorb
/// loop over the `N_BYTES / 136 + 1` rate blocks unrolls completely.
///
/// ## Byte → lane mapping (matches `keccak256_block` EXACTLY)
///
/// The rate is 136 bytes = 17 lanes × 8 bytes, lanes little-endian. The message
/// byte at absolute position `pos` lands in lane `pos / 8` (here `li` within the
/// block) at the little-endian bit offset `(pos % 8) * 8`; the byte's own 8 bits
/// are little-endian (`Field::to_bits::<8>`, bit 0 = LSB). This reproduces the
/// empty-message padded block used by `keccak256_block`: `0x01` at byte 0 sets
/// lane-0 bit 0 (`w0 = 1`) and `0x80` at byte 135 sets lane-16 bit 63
/// (`w16 = 2^63`).
///
/// ## Padding (`pad10*1`, Ethereum 0x01 … 0x80)
///
/// The padded length is `L = (N_BYTES / 136 + 1) * 136` bytes. Byte `N_BYTES`
/// gets `0x01` (LSB of its slot), the final byte `L-1` gets `0x80` (bit 7 of its
/// slot). If they coincide (single pad byte) the byte is `0x81` (both bits set).
///
/// ## Range checking
///
/// Each `msg` element is a byte; `to_bits::<8>` boolean-constrains and pins its
/// 8 bits, proving `msg[i] < 256`, so the witness cannot smuggle a wide value.
///
/// Returns the 4 digest lanes (each a `[Field; 64]` little-endian word).
pub fn keccak256<const N_BYTES: usize>(msg: [Field; N_BYTES]) -> [[Field; 64]; 4] {
    let zero = [Field::from(0u8); 64];

    // Compile-time block count and padded byte length (const-folded).
    let n_blocks = N_BYTES / 136usize + 1usize;
    let padded_len = n_blocks * 136usize;

    // Sponge state: 25 zero lanes.
    let mut state = [zero; 25];

    let mut blk = 0usize;
    while blk < n_blocks {
        // Build this block's 17 rate lanes as bit arrays, then XOR into the rate
        // lanes of the state (capacity lanes 17..25 are never touched).
        let mut li = 0usize;
        while li < 17usize {
            let mut lane = zero;
            let mut k = 0usize;
            while k < 8usize {
                let pos = blk * 136usize + li * 8usize + k;
                if pos < N_BYTES {
                    // Witness byte: range-checked to 0..256, split into 8 LE bits,
                    // placed at the byte's little-endian slot in the lane.
                    let bits = msg[pos].to_bits::<8>();
                    let mut b = 0usize;
                    while b < 8usize {
                        lane[k * 8usize + b] = bits[b];
                        b += 1;
                    }
                } else {
                    // Padding region: compile-time-constant bytes (0x00/0x01/0x80/0x81).
                    if pos == N_BYTES {
                        lane[k * 8usize] = Field::from(1u8); // 0x01 domain byte
                    }
                    if pos == padded_len - 1usize {
                        lane[k * 8usize + 7usize] = Field::from(1u8); // 0x80 final bit
                    }
                }
                k += 1;
            }
            // state[li] ^= lane. For the first block state[li] is the zero
            // constant, so each XOR folds to no gate (identical to absorbing).
            let cur = read25(state, li);
            let nl = xor64(cur, lane);
            let mut b = 0usize;
            while b < 64usize {
                state[li][b] = nl[b];
                b += 1;
            }
            li += 1;
        }
        state = keccak_f(state);
        blk += 1;
    }

    // Squeeze the first 256 bits = lanes 0..4.
    let mut out = [zero; 4];
    let mut i = 0usize;
    while i < 4usize {
        let mut j = 0usize;
        while j < 64usize {
            out[i][j] = state[i][j];
            j += 1;
        }
        i += 1;
    }
    out
}
/// Bring the gadget's public API into scope alongside the xark circuit
/// essentials (`Field`, `Public`/`Private`, `assert_eq`, `#[circuit]`), so a
/// circuit crate needs a single `use xark_keccak::prelude::*;`.
pub mod prelude {
    pub use crate::*;
    pub use xark::prelude::*;
}
