//! `xark-poseidon`: a Poseidon permutation gadget over state width `t = 3`
//! with the `alpha = 5` S-box, written entirely in the `Field` subset.
//!
//! Circuit authors just `use xark_poseidon::hash2;` — the compiler inlines the
//! whole permutation, so it lowers to the same R1CS as if it were written
//! inline. Bounded `while` loops are unrolled at compile time and `[Field; 3]`
//! arrays / helper `fn`s all compose.
//!
//! ## Parameters (TOY / NON-CRYPTOGRAPHIC)
//!
//! The round constants and MDS matrix below are **placeholders** chosen for
//! clarity, NOT security. Real Poseidon for BN254 uses field-sized round
//! constants and an MDS matrix derived from a Cauchy/Vandermonde construction
//! (see the reference Poseidon paper). Swapping in real constants does not
//! change the *circuit structure* (gate count), only the constant values, so
//! this gadget is structurally faithful to the real permutation.
//!
//! - `t   = 3`  (state width)
//! - `R_F = 4`  (full rounds: 2 before + 2 after the partial rounds)
//! - `R_P = 2`  (partial rounds)
//! - total rounds = 6
//! - S-box: `x^5` (`alpha = 5`)
//! - MDS: fixed toy matrix `[[2,3,1],[1,2,3],[3,1,2]]`
//!
//! ## Cost model
//!
//! Only `variable * variable` products emit an R1CS gate. `constant * variable`,
//! `+`, and `-` fold into linear combinations for free. Therefore:
//! - ARK (adding constant round keys) is FREE.
//! - MDS (a constant-matrix * state product) is FREE.
//! - The ONLY gates come from the S-boxes. `x^5` lowers by repeated squaring:
//!   `x^2` (1 gate), `x^4 = x^2 * x^2` (1 gate), `x^5 = x^4 * x` (1 gate) = 3
//!   gates.
//!
//! With `t = 3`, a full round has 3 S-boxes (9 gates); a partial round has 1
//! S-box (3 gates). So `R_F` full + `R_P` partial rounds cost
//! `4*9 + 2*3 = 42` multiplication gates.
//!
//! ## Subset gotcha
//!
//! Loop bounds must be integer *literals* (`while i < 3usize`), not named
//! `const`s: the unroller resolves the branch by tracking integer *locals*, and
//! a comparison against a named const reads as witness-dependent control flow
//! and is rejected. `T` is therefore used only as an array length, never as a
//! loop bound.

#![no_std]
// Circuit-lowered gadget code: the xark compiler rejects compound assignment on
// `Field` (`+=`/`-=`/`*=`), so `x = x + y` is required — not a clippy oversight.
#![allow(clippy::assign_op_pattern)]

use xark::Field;

/// State width.
const T: usize = 3;

/// The Poseidon S-box for `alpha = 5`: `x^5`.
///
/// Lowers to 3 multiplication gates via repeated squaring.
fn sbox(x: Field) -> Field {
    x ^ 5
}

/// ARK (add round key): add the round key `c` to the state element-wise.
///
/// Constant adds fold into the linear combination, so this emits ZERO gates.
fn ark(state: [Field; T], c: [Field; T]) -> [Field; T] {
    let mut out = state;
    let mut i = 0usize;
    while i < 3usize {
        out[i] = state[i] + c[i];
        i += 1;
    }
    out
}

/// MDS (linear mixing): multiply the state by the fixed toy MDS matrix
/// `M = [[2,3,1],[1,2,3],[3,1,2]]`.
///
/// Every matrix entry is a compile-time constant, so each `M[i][j] * state[j]`
/// is a `constant * variable` scale that folds into the linear combination.
/// This linear layer therefore emits ZERO gates.
fn mds(state: [Field; T]) -> [Field; T] {
    let c1 = Field::from(1u8);
    let c2 = Field::from(2u8);
    let c3 = Field::from(3u8);
    [
        c2 * state[0] + c3 * state[1] + c1 * state[2], // row [2,3,1]
        c1 * state[0] + c2 * state[1] + c3 * state[2], // row [1,2,3]
        c3 * state[0] + c1 * state[1] + c2 * state[2], // row [3,1,2]
    ]
}

/// A full round: ARK, then apply the S-box to ALL `t` state elements, then MDS.
///
/// Cost: `t` S-boxes = `3 * 3 = 9` gates.
fn full_round(state: [Field; T], c: [Field; T]) -> [Field; T] {
    let mut s = ark(state, c);
    let mut i = 0usize;
    while i < 3usize {
        s[i] = sbox(s[i]);
        i += 1;
    }
    mds(s)
}

/// A partial round: ARK, then apply the S-box to `state[0]` ONLY, then MDS.
///
/// Cost: 1 S-box = 3 gates.
fn partial_round(state: [Field; T], c: [Field; T]) -> [Field; T] {
    let mut s = ark(state, c);
    s[0] = sbox(s[0]);
    mds(s)
}

/// The Poseidon permutation on a width-3 state.
///
/// Round schedule (`R_F = 4`, `R_P = 2`): 2 full rounds, then 2 partial rounds,
/// then 2 full rounds. Round constants are toy placeholders — the running
/// counter `1, 2, ..., 18` written out as decimal-string field constants (18
/// constants for 6 rounds * 3 lanes). Replace with real constants for a
/// cryptographic instantiation.
///
/// Note: each round is a fresh `let s = ...` binding (shadowing) rather than a
/// reassigned `let mut`; threading the state by value through the inlined round
/// helpers keeps the unroller's data-flow simple.
pub fn permute(state: [Field; T]) -> [Field; T] {
    // Per-round constant vectors (toy: increasing integers 1..=18), one
    // `[Field; 3]` round key per round.
    let rc0 = [Field::from(1u8), Field::from(2u8), Field::from(3u8)];
    let rc1 = [Field::from(4u8), Field::from(5u8), Field::from(6u8)];
    let rc2 = [Field::from(7u8), Field::from(8u8), Field::from(9u8)];
    let rc3 = [Field::from(10u8), Field::from(11u8), Field::from(12u8)];
    let rc4 = [Field::from(13u8), Field::from(14u8), Field::from(15u8)];
    let rc5 = [Field::from(16u8), Field::from(17u8), Field::from(18u8)];

    // First half: 2 full rounds.
    let s = full_round(state, rc0);
    let s = full_round(s, rc1);

    // Middle: 2 partial rounds.
    let s = partial_round(s, rc2);
    let s = partial_round(s, rc3);

    // Second half: 2 full rounds.
    let s = full_round(s, rc4);
    full_round(s, rc5)
}

/// 2-to-1 compression: absorb `a` and `b` alongside a capacity element `0`, run
/// the permutation once, and squeeze the first state element.
///
/// ⚠️ **NON-CRYPTOGRAPHIC** — toy parameters (see the crate-level warning). Use
/// `xark-poseidon2` for a real Poseidon2-BN254 hash. `hash2(a, b) = permute([0, a, b])[0]`.
pub fn hash2(a: Field, b: Field) -> Field {
    let out = permute([Field::from(0u8), a, b]);
    out[0]
}

/// Variable-length hash of `N` field elements via a Poseidon **sponge** (rate 2,
/// capacity 1). `N` is a compile-time constant (a circuit is fixed-size), so the
/// absorb loop unrolls.
///
/// ⚠️ **NON-CRYPTOGRAPHIC** — toy parameters (see the crate-level warning); use
/// `xark-poseidon2` for a real hash.
///
/// Capacity lane is `state[0]` (seeded with the length `N` for domain
/// separation); the rate lanes are `state[1..3]`. Inputs are absorbed two at a
/// time by *adding* into the rate lanes and permuting; a final partial pair is
/// zero-padded; `state[0]` is squeezed as the digest.
pub fn hash<const N: usize>(inputs: [Field; N]) -> Field {
    let mut state = [Field::from(N as u64), Field::from(0u8), Field::from(0u8)];
    let mut i = 0usize;
    while i < N {
        state[1] = state[1] + inputs[i];
        if i + 1 < N {
            state[2] = state[2] + inputs[i + 1];
        }
        state = permute(state);
        i += 2;
    }
    state[0]
}
